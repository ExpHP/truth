

pub fn gen_ast_macros() -> String {
    vec![
        gen_ast_macro(
            "expr_binop", &[
                ("a", ArgKind::Node),
                ("op", ArgKind::Token),
                ("b", ArgKind::Node),
            ],
            "$crate::ast::Expr::Binop(
                Box::new($a), $op, Box::new($b),
            )",
        ),

        gen_ast_macro(
            "expr_unop", &[
                ("op", ArgKind::Token),
                ("b", ArgKind::Node),
            ],
            "$crate::ast::Expr::Unop(
                $op, Box::new($b),
            )",
        ),

        gen_ast_macro(
            "stmt_assign", &[
                ("time", ArgKind::StmtTime),
                ("var", ArgKind::Node),
                ("op", ArgKind::Token),
                ("value", ArgKind::Node),
            ],
            "$crate::ast::Stmt {
                time: $time,
                body: $crate::ast::StmtBody::Assignment {
                    var: $var, op: $op, value: $value,
                },
            }",
        ),

        gen_ast_macro(
            "stmt_label", &[
                ("time", ArgKind::StmtTime),
                ("label", ArgKind::Node),
            ],
            "$crate::ast::Stmt {
                time: $time,
                body: $crate::ast::StmtBody::Label($label.clone()),
            }",
        ),

        gen_ast_macro(
            "stmt_goto", &[
                ("time", ArgKind::StmtTime),
                ("keyword", ArgKind::Token),
                ("cond", ArgKind::Node),
                ("goto_label", ArgKind::GotoLabel),
                ("goto_time", ArgKind::GotoTime),
            ],
            "$crate::ast::Stmt {
                time: $time,
                body: $crate::ast::StmtBody::Jump($crate::ast::StmtGoto {
                    destination: $goto_label, time: $goto_time,
                }),
            }",
        ),

        gen_ast_macro(
            "stmt_cond_goto", &[
                ("time", ArgKind::StmtTime),
                ("keyword", ArgKind::Token),
                ("cond", ArgKind::Node),
                ("goto_label", ArgKind::GotoLabel),
                ("goto_time", ArgKind::GotoTime),
            ],
            "$crate::ast::Stmt {
                time: $time,
                body: $crate::ast::StmtBody::CondJump {
                    keyword: $keyword,
                    cond: $cond,
                    jump: $crate::ast::StmtGoto {
                        destination: $goto_label, time: $goto_time,
                    },
                },
            }",
        ),
    ].iter().map(|s| s.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}

use std::fmt;

#[derive(Debug, Copy, Clone)]
enum ArgKind {
    StmtTime,
    Token,
    Node,
    GotoLabel,
    GotoTime,
}

fn make_case(mac: &str, cur_step: &str, next_step: &str, to_parse: &str, to_save: &str) -> Rule {
    Rule {
        pattern: format!(
            "@{cur_step} [{to_parse} $($rest:tt)*] $($done:tt)*",
            cur_step=cur_step, to_parse=to_parse,
        ),
        result: format!(
            "_{mac}_impl!{{ @{next_step} [$($rest)*] $($done)* [{to_save}] }}",
            mac=mac, next_step=next_step, to_save=to_save,
        ),
    }
}
fn make_err_case(cur_step: &str, expected: &str) -> Rule {
    Rule {
        pattern: format!(
            "@{cur_step} [$($first:tt $($rest:tt)*)?] $($done:tt)*",
            cur_step=cur_step,
        ),
        result: format!(
            r#"_truth__compile_error!{{
                _truth__concat!(
                    "in {cur_step}: expected {expected}",
                    $(", got '", _truth__stringify!($first), "'")?
                )
            }}"#,
            expected=expected, cur_step=cur_step,
        ),
    }
}

impl ArgKind {
    fn gen_cases(&self, out: &mut Vec<Rule>, mac: &str, cur_step: &str, next_step: &str) {
        let case = |to_parse: &str, to_save: &str| make_case(mac, cur_step, next_step, to_parse, to_save);
        let err = |msg: &str| make_err_case(cur_step, msg);
        match self {
            ArgKind::StmtTime => {
                out.push(case(&format!("at $time:expr,"), ""));
                out.push(err(&format!("'at <time>,'")));
            },
            ArgKind::Node => {
                out.push(case(&format!("($expr:expr)"), "$expr"));
                out.push(case(&format!("$krate:ident::$mac:ident!$args:tt"), "$krate::$mac!$args"));
                out.push(case(&format!("$mac:ident!$args:tt"), "$mac!$args"));
                out.push(case(&format!("$var:ident"), "$var"));
                out.push(err(&format!("a macro invocation, a local variable, or a parenthesized expression")));
            },
            ArgKind::Token => {
                out.push(case(&format!("($expr:expr)"), "$expr"));
                out.push(case(&format!("$krate:ident::$mac:ident!$args:tt"), "$krate::$mac!$args"));
                out.push(case(&format!("$mac:ident!$args:tt"), "$mac!$args"));
                out.push(case(&format!("$var:ident"), "$var"));
                out.push(case(&format!("$token:tt"), "token!($token)"));
                out.push(err(&format!("a macro invocation, a local variable, a parenthesized expression, or an operator")));
            },
            ArgKind::GotoLabel => {
                out.push(case(&format!("goto ($expr:expr)"), "$expr"));
                out.push(case(&format!("goto $krate:ident::$mac:ident!$args:tt"), "$krate::$mac!$args"));
                out.push(case(&format!("goto $mac:ident!$args:tt"), "$mac!$args"));
                out.push(case(&format!("goto $var:ident"), "$var"));
                out.push(err(&format!("goto label")));
            },
            ArgKind::GotoTime => {
                out.push(case(&format!("@ ($expr:expr)"), "Some($expr)"));
                out.push(case(&format!("@ $var:ident"), "Some($var)"));
                out.push(case(&format!(""), "None"));
                out.push(err(&format!("an optional '@ time'")));
            },
        }
    }

    fn rec_sp_step_pieces(&self, name: &str) -> (String, String) {
        match self {
            // cases for things that can receive spans recursively.  We need to match as `:tt*`
            // so that inner macro calls are still transparent.
            ArgKind::Token => (format!("$(${}:tt)*", name), format!("rec_sp!(span => $(${})*)", name)),
            ArgKind::Node => (format!("$(${}:tt)*", name), format!("rec_sp!(span => $(${})*)", name)),
            // Cases for things that don't need spans.
            ArgKind::StmtTime => (format!("${}:expr", name), format!("${}", name)),
            ArgKind::GotoLabel => (format!("${}:expr", name), format!("${}", name)),
            ArgKind::GotoTime => (format!("${}:expr", name), format!("${}", name)),
        }
    }
}

fn gen_ast_macro(mac: &str, steps: &[(&str, ArgKind)], final_expr: &str) -> String {
    let first_step_name = steps[0].0;
    let main_macro = MacroRules {
        name: format!("{}", mac),
        rules: vec![
            // A rule that sets aside the span from rec_sp! so it can be recursively applied to arguments.
            Rule {
                pattern: format!("rec_sp!($span:expr => $($input:tt)+)"),
                result: format!("_{}_impl!{{ @parse_{}[$($input)+] [$span] }}", mac, first_step_name),
            },
            // Rule with no span
            Rule {
                pattern: format!("$($input:tt)+"),
                result: format!("_{}_impl!{{ @parse_{}[$($input)+] [] }}", mac, first_step_name),
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
        parts_in.push_str(&format!("[{}] ", pat));
        parts_out.push_str(&format!("[{}] ", out));
    }

    impl_macro.rules.push(Rule {
        pattern: format!("@finish[] [$span:expr] {}", parts_in),
        result: format!(r#"
            match $span {{
                span => _{mac}_impl!{{ @finish[] [] {parts_out} }},
            }}
        "#, mac=mac, parts_out=parts_out),
    });

    // case that produces the final output
    let final_case_pats = {
        steps.iter().map(|(name, _)| format!("[${}:expr]", name))
            .collect::<Vec<_>>()
            .join(" ")
    };
    impl_macro.rules.push(Rule {
        pattern: format!("@finish[] [] {}", final_case_pats),
        result: final_expr.to_string(),
    });

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
