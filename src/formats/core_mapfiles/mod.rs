use ::std::collections::BTreeMap;

use crate::game::Game;
use crate::eclmap::Eclmap;

pub mod anm;
pub mod msg;
pub mod std;

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
pub struct CoreSignatures {
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
    ins: &'static [(Game, u16, Option<&'static str>)],

    /// Like [`Self::ins`] but for registers.
    var: &'static [(Game, i32, Option<&'static str>)],
}

impl CoreSignatures {
    pub fn to_mapfile(&self, game: Game) -> Eclmap {
        let mut mapfile = Eclmap::new();
        self.apply_to_mapfile(game, &mut mapfile);
        mapfile
    }

    fn apply_to_mapfile(&self, game: Game, mapfile: &mut Eclmap) {
        for parent in self.inherit {
            parent.apply_to_mapfile(game, mapfile);
        }

        for &(min_game, opcode, siggy_str) in self.ins {
            if min_game <= game {
                insert_or_remove(&mut mapfile.ins_signatures, opcode as _, siggy_str);
            }
        }

        for &(min_game, reg_id, type_str) in self.var {
            if min_game <= game {
                insert_or_remove(&mut mapfile.gvar_types, reg_id as _, type_str);
            }
        }
    }
}

fn insert_or_remove<K, V>(map: &mut BTreeMap<K, V::Owned>, key: K, value: Option<&V>)
where
    K: Ord + Eq,
    V: ToOwned + ?Sized,
{
    if let Some(value) = value {
        map.insert(key, value.to_owned());
    } else {
        map.remove(&key);
    }
}
