use crate::raw;
use crate::pos::{Sp, SourceStr};
use crate::game::{Game, LanguageKey};
use crate::mapfile::Mapfile;
use crate::error::ErrorReported;
use crate::diagnostic::RootEmitter;

mod anm;
mod ecl;
mod msg;
mod std;

/// Obtain a mapfile with signatures and types for all vanilla instructions and registers
/// for a single InstrLanguage.
pub fn core_mapfile(emitter: &RootEmitter, game: Game, language: LanguageKey) -> Mapfile {
    let signatures = match language {
        LanguageKey::Anm => self::anm::core_signatures(game),
        LanguageKey::Std => self::std::core_signatures(game),
        LanguageKey::Msg => self::msg::core_signatures(game),
        LanguageKey::Ecl => self::ecl::core_signatures(game),
        LanguageKey::Timeline => self::ecl::timeline_core_signatures(game),
        LanguageKey::End => CoreSignatures::EMPTY, // TODO
        LanguageKey::Dummy => CoreSignatures::EMPTY,
    };

    let mapfile = signatures.to_mapfile(language, game);
    add_spans_to_core_mapfile(emitter, &mapfile)
}

/// Struct for representing some embedded mapfile information (notably the default signatures and
/// register types for all mainstream games).
///
/// Basically, the current mapfile syntax has a bit of a problem that it is impossible to factor
/// out into reusable parts.  And since some formats frequently change signatures of individual
/// instructions, putting signatures there requires maintaining an unduly amount of copy-pasta.
///
/// This internal data structure is designed to be easier to refactor and maintain compared to
/// an actual mapfile, and in the future may even help guide attempts to solve the factoring
/// problem for user mapfile syntax.
struct CoreSignatures {
    /// A simple method of factoring out a single [`CoreSignatures`] into reusable
    /// portions when other methods fail to suffice. There's no specific, prescribed usage.
    ///
    /// Each item listed here will be applied in sequence before the definitions contained on
    /// the struct itself. (with later values overriding earlier ones)
    ///
    /// Note that a significant amount of boilerplate can be avoided by making use of the
    /// "minimum game" fields on [`Self::ins`] and [`Self::var`], and so some formats don't
    /// actually need to make use of this at all.
    inherit: &'static [&'static CoreSignatures],

    /// A set of tuples, each the addition of a new instruction or the change of an existing
    /// instruction's signature in some game.  (a `None` indicates removal; i.e. the jumptable
    /// entry now points to the default branch)
    ///
    /// The strings are mapfile string signatures.
    ///
    /// When converted to a mapfile, the program will run down this list and apply each item
    /// from the current game or earlier.  The presence of these "minimum game" fields allows
    /// a single [`CoreSignatures`] to be easily applied to an entire range of games.
    ins: &'static [(Game, raw::Opcode, Option<&'static str>)],

    /// Like [`Self::ins`] but for registers.
    var: &'static [(Game, raw::Register, Option<&'static str>)],
}

impl CoreSignatures {
    const EMPTY: &'static Self = &CoreSignatures {
        inherit: &[], ins: &[], var: &[],
    };

    fn to_mapfile(&self, language: LanguageKey, game: Game) -> Mapfile {
        let mut mapfile = Mapfile::new_core_mapfile(language);
        self.apply_to_mapfile(game, &mut mapfile);
        mapfile
    }

    fn apply_to_mapfile(&self, game: Game, mapfile: &mut Mapfile) {
        for parent in self.inherit {
            parent.apply_to_mapfile(game, mapfile);
        }

        for &(min_game, opcode, siggy_str) in self.ins {
            if min_game <= game {
                insert_or_remove(&mut mapfile.ins_signatures, opcode as _, siggy_str.map(|x| sp!(x)));
            }
        }

        for &(min_game, reg_id, type_str) in self.var {
            if min_game <= game {
                insert_or_remove(&mut mapfile.gvar_types, reg_id as _, type_str.map(|x| sp!(x)));
            }
        }
        check_core_mapfile_invariants(mapfile);
    }
}

// Even though mapfiles are backed by Vecs to allow duplicates, core mapfiles are more maplike
// so that information from later games can replace information from earlier games.
fn check_core_mapfile_invariants(mapfile: &Mapfile) {
    for map in [&mapfile.ins_signatures, &mapfile.gvar_types] {
        assert!(map.windows(2).all(|window| window[0].0 < window[1].0), "core mapfile not sorted or has duplicate");
    }
}

fn insert_or_remove<K, V>(map: &mut Vec<(K, Sp<V::Owned>)>, key: K, value: Option<Sp<&V>>)
where
    K: Ord + Eq,
    V: ToOwned + ?Sized,
{
    match (value, map.binary_search_by_key(&&key, |(item_key, _)| item_key)) {
        (None, Ok(index)) => { map.remove(index); },
        (None, Err(_)) => {},
        (Some(value), Ok(index)) => map[index] = (key, value.sp_map(ToOwned::to_owned)),
        (Some(value), Err(index)) => map.insert(index, (key, value.sp_map(ToOwned::to_owned))),
    }
}

/// Bit of a silly hack.
///
/// Core mapfiles are written to text and then parsed back from that text so that it has spans.
///
/// Generally speaking, it is still undesirable to have an error point into a core mapfile as it doesn't
/// reflect something user actionable.  This hack exists mostly so that the ABI parser can assume there
/// are always spans, and so that truth can still print an error instead of crashing in the relatively
/// few instances where it may try to print a span from a core mapfile.
fn add_spans_to_core_mapfile(emitter: &RootEmitter, mapfile: &Mapfile) -> Mapfile {
    _add_spans_to_core_mapfile_imp(emitter, mapfile)
        .expect("shouldn't fail for trusted input!")
}

fn _add_spans_to_core_mapfile_imp(emitter: &RootEmitter, mapfile: &Mapfile) -> Result<Mapfile, ErrorReported> {
    let seqmap = mapfile.to_borrowed_seqmap();
    let text = format!("{seqmap}");
    let (file_id, text) = {
        emitter.files.add(&format!("<builtin {} signatures>", mapfile.language.descr()), text.as_bytes())
            .map_err(|e| emitter.emit(e))?
    };
    let source_str = SourceStr::from_full_source(file_id, &text);
    let seqmap = crate::parse::seqmap::SeqmapRaw::parse(file_id, &text, &emitter)?;

    let mut out = Mapfile::from_seqmap(seqmap, &emitter)?;
    out.is_core_mapfile = true;
    Ok(out)
}
