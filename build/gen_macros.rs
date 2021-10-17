

pub fn gen_ast_macros() -> String {
    vec![
        // ==== Macros that can generate either StmtBody or Stmt ====

        gen_ast_macro(
            "stmt_assign", &[
                ("_as_kind", ArgKind::AsKind),
                ("var", ArgKind::Node),
                ("op", ArgKind::Token(&[
                    "=", "+=", "-=", "*=", "/=", "%=", "|=", "^=", "&="
                ])),
                ("value", ArgKind::Node),
            ],
            FinalCasesType::Stmt { body: r#"
                $crate::ast::StmtBody::Assignment {
                    var: ::core::convert::Into::into($var),
                    op: $op,
                    value: ::core::convert::Into::into($value),
                }
            "#},
        ),

        gen_ast_macro(
            "stmt_label", &[
                ("_as_kind", ArgKind::AsKind),
                ("label", ArgKind::Node),
            ],
            FinalCasesType::Stmt { body: r#"
                $crate::ast::StmtBody::Label($label)
            "#},
        ),

        gen_ast_macro(
            "stmt_goto", &[
                ("_as_kind", ArgKind::AsKind),
                ("goto_label", ArgKind::GotoLabel),
                ("goto_time", ArgKind::GotoTime),
            ],
            FinalCasesType::Stmt { body: r#"
                $crate::ast::StmtBody::Goto($crate::ast::StmtGoto {
                    destination: $goto_label,
                    time: $goto_time,
                })
            "#},
        ),

        gen_ast_macro(
            "stmt_cond_goto", &[
                ("_as_kind", ArgKind::AsKind),
                ("keyword", ArgKind::Token(&["if", "unless"])),
                ("cond", ArgKind::Cond),
                ("goto_label", ArgKind::GotoLabel),
                ("goto_time", ArgKind::GotoTime),
            ],
            FinalCasesType::Stmt { body: r#"
                $crate::ast::StmtBody::CondGoto {
                    keyword: $keyword,
                    cond: Into::into($cond),
                    goto: $crate::ast::StmtGoto {
                        destination: $goto_label,
                        time: $goto_time,
                    },
                }
            "#},
        ),

        gen_ast_macro(
            "stmt_interrupt", &[
                ("_as_kind", ArgKind::AsKind),
                ("number", ArgKind::Node),
            ],
            FinalCasesType::Stmt { body: r#"
                $crate::ast::StmtBody::InterruptLabel($number)
            "#},
        ),

        // ==== Macros to generate Exprs ====

        gen_ast_macro(
            "expr_binop", &[
                ("a", ArgKind::Node),
                ("op", ArgKind::Token(&[
                    "+", "-", "*", "/", "%",
                    "==", "!=", "<", "<=", ">", ">=",
                    "|", "^", "&", "||", "&&",
                ])),
                ("b", ArgKind::Node),
            ],
            FinalCasesType::Regular(r#"
                $crate::ast::Expr::Binop(
                    Box::new(Into::into($a)),
                    $op,
                    Box::new(Into::into($b)),
                )
            "#),
        ),

        gen_ast_macro(
            "expr_unop", &[
                ("op", ArgKind::Token(&[
                    "-", "!",
                    "sin", "cos", "sqrt",
                    "_S", "_f",
                ])),
                ("b", ArgKind::Node),
            ],
            FinalCasesType::Regular(r#"
                $crate::ast::Expr::Unop(
                    $op,
                    Box::new(Into::into($b)),
                )
            "#),
        ),
    ].iter().map(|s| s.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}

use std::fmt;

#[derive(Debug, Copy, Clone)]
enum ArgKind {
    /// The most standard type of subterm.
    Node,
    /// A node for something that should not get its own span, yet still allows `rec_sp!` to
    /// recurse through it if it is an AST macro call.
    // (this was originally used for the stmt body in e.g. `stmt!(at #time, stmt_label!(#ident))`)
    #[allow(dead_code)]
    SpTransparent,
    /// This allows a keyword or token to be directly written
    Token(&'static [&'static str]),

    // A bunch of things that require special treatment due to e.g. optional parts or extra syntax
    AsKind,
    Cond,
    GotoLabel,
    GotoTime,
}

fn make_case(mac: &str, cur_step: &str, next_step: &str, to_parse: &str, to_save: &str, record_flag: Option<&str>) -> Rule {
    let new_flags = match record_flag {
        Some(flag) => format!(" {}", flag),
        None => format!(""),
    };
    Rule {
        pattern: format!(
            "@{cur_step} flags#[$($flags:ident)*] input#[{to_parse} $($rest:tt)*] $($done:tt)*",
            cur_step=cur_step, to_parse=to_parse,
        ),
        result: format!(
            "_{mac}_impl!{{ @{next_step} flags#[$($flags)*{new_flags}] input#[$($rest)*] $($done)* arg#[{to_save}] }}",
            mac=mac, next_step=next_step, to_save=to_save, new_flags=new_flags,
        ),
    }
}

fn make_err_case_expected_after(cur_step: &str, pattern_prefix: &str, expected: &str) -> Rule {
    make_err_case(cur_step, pattern_prefix, &format!(r#"
        _truth__concat!(
            "in {cur_step}: expected {expected}",
            $(", got '", _truth__stringify!($first), "'")?
        )
    "#, expected=expected, cur_step=cur_step))
}

fn make_err_case_expected(cur_step: &str, expected: &str) -> Rule {
    make_err_case_expected_after(cur_step, "", expected)
}

fn make_err_case(cur_step: &str, pattern_prefix: &str, msg: &str) -> Rule {
    let pattern = format!(
        "@{cur_step} flags#[$($flags:ident)*] input#[{prefix} $($first:tt $($rest:tt)*)?] span#$span:tt $($first_done:tt $($done:tt)*)?",
        cur_step=cur_step, prefix=pattern_prefix,
    );
    let debug_heading = "\n Things parsed so far:  ";
    let debug_spacing = "\n                        ";
    let debug_report = format!(
        r#"$( {:?}, _truth__stringify!($first_done) $(, {:?}, _truth__stringify!($done))* )?"#, debug_heading, debug_spacing,
    );
    let result = format!("_truth__compile_error!{{ _truth__concat!( {}, {} ) }}", msg, debug_report);
    Rule { pattern, result }
}

const MAC_OR_INTERP: &'static str = "an AST macro invocation 'mac!(...)', an interpolated variable '#var', or an interpolated expression '#(...)'";
const MAC_INTERP_OR_TOKEN: &'static str = "a macro invocation 'mac!(...)', an interpolated variable '#var', an interpolated expression '#(...)', or a keyword/operator '+'";
const JUST_INTERP: &'static str = "an interpolated variable '#var', or an interpolated expression '#(...)'";

impl ArgKind {
    fn gen_cases(&self, out: &mut Vec<Rule>, mac: &str, cur_step: &str, next_step: &str) {
        let case = |to_parse: &str, to_save: &str, flag: Option<&str>| make_case(mac, cur_step, next_step, to_parse, to_save, flag);
        let expected = |msg: &str| make_err_case_expected(cur_step, msg);
        let expected_after = |prefix: &str, msg: &str| make_err_case_expected_after(cur_step, prefix, msg);
        let err = |msg: &str| make_err_case(cur_step, "", msg);

        const DUMMY_EXPR: &'static str = r#"unreachable!("unused dummy time")"#;
        match self {
            ArgKind::Node |
            ArgKind::SpTransparent => {
                // these are the types of syntax that rec_sp! can recurse into.
                out.push(case(&format!("#($expr:expr)"), "$expr", None));
                out.push(case(&format!("#$var:ident"), "$var", None));
                out.push(case(&format!("$mac:ident!$args:tt"), "$mac!$args", None));
                out.push(expected(MAC_OR_INTERP));
            },
            ArgKind::AsKind => {
                // lets us know to create a StmtKind instead of a Stmt
                out.push(case(&format!("as kind,"), DUMMY_EXPR, Some("as_kind")));
                out.push(case(&format!(""), DUMMY_EXPR, Some("")));
            },
            ArgKind::Cond => {
                // NOTE: Sp<Expr> implements Into<Sp<Cond>> so we don't need special snytax for it
                out.push(case(&format!("(decvar: #($expr:expr))"), "_ast_map!($crate::ast::Cond::PreDecrement, $expr)", None));
                out.push(case(&format!("(decvar: #$var:ident)"), "_ast_map!($crate::ast::Cond::PreDecrement, $var)", None));
                out.push(case(&format!("(decvar: $mac:ident!$args:tt)"), "_ast_map!($crate::ast::Cond::PreDecrement, $mac!$args)", None));
                out.push(case(&format!("#($expr:expr)"), "$expr", None));
                out.push(case(&format!("#$var:ident"), "$var", None));
                out.push(case(&format!("$mac:ident!$args:tt"), "$mac!$args", None));
                out.push(err(&format!("{:?}", format!("conditionals need to be written as 'if <cond>' or 'if (decvar: <var>)', where <var>/<cond> can be {}", MAC_OR_INTERP))));
            },
            ArgKind::Token(tokens) => {
                out.push(case(&format!("#($expr:expr)"), "$expr", None));
                out.push(case(&format!("#$var:ident"), "$var", None));
                out.push(case(&format!("$mac:ident!$args:tt"), "$mac!$args", None));
                for token in tokens.iter() {
                    out.push(case(token, &format!("token!({})", token), None));
                }
                out.push(expected(MAC_INTERP_OR_TOKEN));
            },
            ArgKind::GotoLabel => {
                out.push(case(&format!("goto #($expr:expr)"), "$expr", None));
                out.push(case(&format!("goto #$var:ident"), "$var", None));
                out.push(case(&format!("goto $mac:ident!$args:tt"), "$mac!$args", None));
                out.push(expected_after("goto", MAC_OR_INTERP));
                out.push(expected(&format!("'goto <label>', where label is {}", MAC_OR_INTERP)));
            },
            ArgKind::GotoTime => {
                out.push(case(&format!("@ #($expr:expr)"), "Some($expr)", None));
                out.push(case(&format!("@ #$var:ident"), "Some($var)", None));
                out.push(expected_after("@", JUST_INTERP));
                out.push(case(&format!("#($expr:expr)"), "$expr", None));
                out.push(case(&format!("#$var:ident"), "$var", None));
                out.push(case(&format!(""), "None", None));
                out.push(expected(&format!("an optional '@ <time>' or '<time>', where <time> is {}", JUST_INTERP)));
            },
        }
    }

    fn rec_sp_step_pieces(&self, name: &str) -> (String, String) {
        match self {
            // Cases for things that can receive spans recursively.  We need to match as `:tt*`
            // so that inner macro calls are still transparent.
            | ArgKind::Token(_)
            | ArgKind::Node
            | ArgKind::Cond
            | ArgKind::GotoLabel
                => (format!("$(${}:tt)*", name), format!("rec_sp!(_span => $(${})*)", name)),

            | ArgKind::SpTransparent
                => (format!("$(${}:tt)*", name), format!("rec_sp!(_span => _ast_sp_transparent!($(${})*))", name)),

            // Cases for things that don't need spans.
            | ArgKind::AsKind
            | ArgKind::GotoTime
                => (format!("${}:expr", name), format!("${}", name)),
        }
    }
}

enum FinalCasesType {
    /// Have the final rule match all of the subexpressions as `$<name>` and then produce whatever
    /// result is contained in the string. (which will basically be the RHS of the rule)
    Regular(&'static str),

    /// Special final case type for statements, which can produce `StmtKind` if the user wrote `as kind,`.
    Stmt { body: &'static str },
}

impl FinalCasesType {
    fn gen_final_rules(&self, out: &mut Vec<Rule>, steps: &[(&str, ArgKind)]) {
        let get_steps_as_exprs = |steps: &[(&str, ArgKind)]| {
            steps.iter().map(|(name, _)| format!("arg#[${}:expr]", name))
                .collect::<Vec<_>>()
                .join(" ")
        };
        match self {
            FinalCasesType::Regular(final_expr) => {
                out.push(Rule {
                    pattern: format!("@finish flags#[] input#[] span#[] {}", get_steps_as_exprs(steps)),
                    result: final_expr.to_string(),
                });
            },
            FinalCasesType::Stmt { body: body_expr } => {
                let time_name = steps[0].0;
                out.push(Rule {
                    pattern: format!("@finish flags#[] input#[] span#[] arg#[${}:expr] {}", time_name, get_steps_as_exprs(&steps[1..])),
                    result: format!(r#"
                        $crate::ast::Stmt {{
                            node_id: None,
                            body: {},
                        }}
                    "#, body_expr),
                });
                out.push(Rule {
                    pattern: format!("@finish flags#[as_kind] input#[] span#[] arg#[$_{}_unused:expr] {}", time_name, get_steps_as_exprs(&steps[1..])),
                    result: format!("{}", body_expr),
                });
            }
        }
    }
}

fn gen_ast_macro(mac: &str, steps: &[(&str, ArgKind)], final_case: FinalCasesType) -> String {
    let first_step_name = steps[0].0;
    let main_macro = MacroRules {
        name: format!("{}", mac),
        rules: vec![
            // A rule that sets aside the span from rec_sp! so it can be recursively applied to arguments.
            Rule {
                pattern: format!("rec_sp!($span:expr => $($input:tt)+)"),
                result: format!("_{}_impl!{{ @parse_{} flags#[] input#[$($input)+] span#[$span] }}", mac, first_step_name),
            },
            // Rule with no span
            Rule {
                pattern: format!("$($input:tt)+"),
                result: format!("_{}_impl!{{ @parse_{} flags#[] input#[$($input)+] span#[] }}", mac, first_step_name),
            },
        ]
    };

    // The rest happens in the "impl" macro, which is an incremental muncher.
    let mut impl_macro = MacroRules {
        name: format!("_{}_impl", mac),
        rules: vec![],
    };
    let next_steps = {
        steps.iter().skip(1)
            .map(|&(name, _)| format!("parse_{}", name))
            .chain(std::iter::once("finish".into()))
    };

    // Each "step" parses one thing through one or more possible different rules,
    // based on ArgKind, then goes to the next step.
    for (&(name, arg_kind), next_step) in steps.iter().zip(next_steps) {
        let cur_step = format!("parse_{}", name);
        arg_kind.gen_cases(&mut impl_macro.rules, mac, &cur_step, &next_step);
    }

    // case that recursively applies rec_sp!()
    let mut parts_in = String::new();
    let mut parts_out = String::new();
    for (name, arg_kind) in steps {
        let (pat, out) = arg_kind.rec_sp_step_pieces(name);
        parts_in.push_str(&format!("arg#[{}] ", pat));
        parts_out.push_str(&format!("arg#[{}] ", out));
    }

    impl_macro.rules.push(Rule {
        pattern: format!("@finish flags#[$($flags:ident)*] input#[] span#[$span:expr] {}", parts_in),
        result: format!(r#"
            match $span {{
                _span => _{mac}_impl!{{ @finish flags#[$($flags)*] input#[] span#[] {parts_out} }},
            }}
        "#, mac=mac, parts_out=parts_out),
    });

    // case(s) that produces the final output
    final_case.gen_final_rules(&mut impl_macro.rules, steps);

    // https://users.rust-lang.org/t/having-helper-macros-call-each-other-in-generated-code/54212
    //
    // I found that it was basically impossible to simultaneously meet all of these requirements:
    //
    // * calling other "helper" macros
    // * referring to non-macro items in the crate via $crate::
    // * being usable in the same crate that defines these items
    // * having downstream code `use` only the macros they call
    //
    // so I dropped the fourth requirement.  That's why these macros don't use $crate::mac! and they
    // don't use local_inner_macros.  Basically, the only sane way to use these macros is through
    // 2015-style #[macro_use].
    format!(r#"
#[macro_export]
{}
#[doc(hidden)]
#[macro_export]
{}"#, main_macro, impl_macro)
}

struct MacroRules {
    name: String,
    rules: Vec<Rule>,
}

struct Rule {
    pattern: String,
    result: String,
}

impl fmt::Display for MacroRules {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "macro_rules! {} {{", self.name)?;
        for rule in &self.rules {
            writeln!(f, "{}", rule)?;
        }
        writeln!(f, "}}")
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}) => {{{}}};", self.pattern, self.result)
    }
}
