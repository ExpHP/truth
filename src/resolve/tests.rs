use crate::pos::Files;
use crate::parse::Parse;
use crate::fmt::Format;
use crate::error::CompileError;
use crate::eclmap::Eclmap;
use crate::context::CompilerContext;
use crate::ast;

const ECLMAP: &'static str = r#"!eclmap
!gvar_names
100 ALIAS
101 XLIAS
!gvar_types
100 $
101 %
!ins_names
21 alias
"#;

macro_rules! test {
    (
        // Create a test that uses passes::debug::make_idents_unique to append numerical suffixes to each
        // resolvable identifier, and use `insta` to let a human review this output to verify that the
        // suffixes correctly disambiguate each identifier.
        //
        // (ideally this wouldn't require human intervention, but there's issues with equating either
        //  strings (due to formatting) or AST nodes (due to ResId))
        [snapshot]
        $name:ident = <$ty:ty> $source:literal
    ) => {
        #[test]
        fn $name() { assert_snapshot!(resolve_reformat::<$ty>($source).trim()); }
    };

    (
        // Automated form of the [snapshot] test used when all names in the source code are unique.
        // (i.e. the only suffix that would have been added to each ident is `_0`)
        [all_names_unique]
        $name:ident = <$ty:ty> $source:literal
    ) => {
        #[test]
        fn $name() { check_names_unique::<$ty>($source); }
    };

    (
        // Create a compile-fail snapshot test
        [expect_fail($expected:expr)]
        $name:ident = <$ty:ty> $source:literal) => {
        #[test]
        fn $name() { assert_snapshot!(resolve_expect_err::<$ty>($source, $expected).trim()); }
    };

    (
        // Disable a known broken test.  Wuss.
        [disable]
        $($rest:tt)*
    ) => {};
}

fn resolve<A: ast::Visitable + Parse>(text: &str) -> Result<(A, CompilerContext), (Files, CompileError)> {
    let mut files = Files::new();
    let mut ctx = CompilerContext::new();
    ctx.extend_from_eclmap(None, &Eclmap::parse(ECLMAP).unwrap()).unwrap();

    let mut parsed = files.parse::<A>("<input>", text.as_ref()).unwrap().value;
    crate::passes::resolve_names::assign_res_ids(&mut parsed, &mut ctx).unwrap();
    match crate::passes::resolve_names::run(&parsed, &mut ctx) {
        Ok(()) => Ok((parsed, ctx)),
        Err(e) => Err((files, e)),
    }
}

fn resolve_reformat<A: ast::Visitable + Format + Parse>(text: &str) -> String {
    let (mut parsed, ctx) = resolve::<A>(text).unwrap_or_else(|(files, e)| panic!("{}", e.to_string(&files).unwrap()));

    // add suffixes so we can visualize the effects of name resolution
    crate::passes::debug::make_idents_unique::run(&mut parsed, &ctx.resolutions).unwrap();

    crate::fmt::stringify(&parsed)
}

fn check_names_unique<A: ast::Visitable + Format + Parse>(text: &str) {
    let (mut parsed, ctx) = resolve::<A>(text).unwrap_or_else(|(files, e)| panic!("{}", e.to_string(&files).unwrap()));

    // add suffixes so we can visualize the effects of name resolution
    let count_per_ident = crate::passes::debug::make_idents_unique::run(&mut parsed, &ctx.resolutions).unwrap();

    for (ident, count) in count_per_ident {
        if count != 1 {
            let reformatted = crate::fmt::stringify(&parsed);
            panic!("[all_names_unique] failed on ident '{}'.\nResolved output:\n\n{}", ident, reformatted)
        }
    }
}

fn resolve_expect_err<A: ast::Visitable + Parse>(text: &str, expected: &str) -> String {
    let (files, err) = resolve::<A>(text).err().unwrap();
    let err_msg = err.to_string(&files).unwrap();
    assert!(err_msg.contains(expected), "{}", err_msg);
    err_msg
}

// =========================================================================
// Simple scope tests
//
// These don't reuse any names, so there's only one possibility for resolution.
// The goal is to test whether they can be resolved.

test!(
    [all_names_unique]
    local_basic = <ast::Block> r#"{
    int a = 3;
    int b = a + a;
}"#);

test!(
    [all_names_unique]
    func_basic = <ast::Script> r#"
int foo(int x) {
    return x;
}

script script0 {
    int y = 3;
    foo(y);
}"#);

test!(
    [all_names_unique]
    const_basic = <ast::Script> r#"
const int A = 2;

script script0 {
    int x = A;
}"#);

test!(
    [all_names_unique]
    param_basic = <ast::Script> r#"
void foo(int x) {
    return x;
}"#);

test!(
    [all_names_unique]
    reg_alias_basic = <ast::Block> r#"{
    ins_21(ALIAS, XLIAS);
}"#);

test!(
    [all_names_unique]
    ins_alias_basic = <ast::Block> r#"{
    alias(3, 2.4);
}"#);

test!(
    [all_names_unique]
    func_out_of_order = <ast::Script> r#"
script script0 {
    int x = 3;
    foo(x);
}

int foo(int y) {
    return y;
}"#);

test!(
    [all_names_unique]
    const_out_of_order = <ast::Script> r#"
script script0 {
    int x = A;
}

const int A = 2;
"#);

test!(
    [all_names_unique]
    func_scoped_out_of_order = <ast::Block> r#"{
    if (true) {
        int x = foo();
        if (true) {
            int y = foo();
        }

        int foo() { return 5; }
    }
}"#);

test!(
    [all_names_unique]
    const_scoped_out_of_order = <ast::Block> r#"{
    if (true) {
        int x = A;
        if (true) {
            int y = A;
        }

        const int A = 5;
    }
}"#);

test!(
    [expect_fail("in this scope")]
    local_after_scope_end = <ast::Block> r#"{
    if (true) {
        int a = 4;
        int b = a;  // should be OK
    }
    int c = a;  // should fail at `a`
}"#);

test!(
    [expect_fail("in this scope")]
    const_after_scope_end = <ast::Block> r#"{
    if (true) {
        const int a = 4;
        int b = a;  // should be OK
    }
    int c = a;  // should fail at `a`
}"#);

test!(
    [expect_fail("in this scope")]
    func_after_scope_end = <ast::Block> r#"{
    if (true) {
        int foo() { return 4; }
        int b = foo();  // should be OK
    }
    int c = foo();  // should fail at `foo`
}"#);

test!(
    [expect_fail("in this scope")]
    local_using_itself = <ast::Block> r#"{
    int a = a;  // should fail at second `a`
}"#);

test!(
    [all_names_unique]
    local_using_older_sibling = <ast::Block> r#"{
    // NOTE: We might want to forbid this...
    int x = 2, y = x, z = x + y;
}"#);

test!(
    [all_names_unique]
    scoped_using_each_other = <ast::Block> r#"{
    if (true) {
        const int A = 3;
        int foo() { return bar() + A; }
        int bar() { return foo() + B; }
        const int B = 5;
    }
}"#);

test!(
    // checks mixed accesses (consts using funcs and vice versa) and usage
    // of things from an outer scope
    [all_names_unique]
    scoped_using_each_other_ex = <ast::Block> r#"{
    const int OUTER = 3;
    if (true) {
        const int inner() { return OUTER + INNER; }
        const int INNER = outer() + inner();
    }
    const int outer() { return 3; }
}"#);

test!(
    [expect_fail("in this scope")]
    const_scoped_using_local = <ast::Block> r#"{
    int x = 2;
    const int foo = x;  // should fail at `x`
}"#);

test!(
    [expect_fail("in this scope")]
    func_scoped_using_local = <ast::Block> r#"{
    int x = 2;
    int foo() {
        return x;  // should fail at `x`
    }
}"#);

test!(
    [expect_fail("in this scope")]
    const_scoped_using_outer_local = <ast::Block> r#"{
    int x = 2;
    if (true) {
        const int foo = x;  // should fail at `x`
    }
}"#);

test!(
    [expect_fail("in this scope")]
    func_scoped_using_outer_param = <ast::Block> r#"{
    void foo(int a) {
        int bar() {
            return a;  // should fail at `a`
        }
    }
}"#);

test!(
    // FIXME: Remove the [disable] tag once const params are implemented
    [disable]  // known test failure
    [all_names_unique]
    func_scoped_using_outer_param_const = <ast::Block> r#"{
    void foo(const int a) {
        int bar() {
            return a;  // should miraculously succeed!
        }
    }
}"#);

test!(
    // FIXME: Remove the [disable] tag once default arguments are implemented
    [disable]  // known test failure
    [all_names_unique]
    param_using_outer_const = <ast::Block> r#"{
    int bar(int z = a) {
        return z;
    }
    const int a = 3;
}"#);

test!(
    // FIXME: Remove the [disable] tag once default arguments are implemented
    [disable]  // known test failure
    [expect_fail("in this scope")]
    param_using_outer_local = <ast::Block> r#"{
    int a = 3;
    int bar(int z = a) {  // should fail at `a`
        return z;
    }
}"#);

// =========================================================================
// Shadowing or disjoint tests
//
// Here, names will be used multiple times.  It will be important to check
// the numeric IDs appended to each identifier in the snapshot output to see
// that names are resolved correctly.

test!(
    [snapshot]
    local_shadow = <ast::Block> r#"{
    int a = 3;
    if (true) {
        int a = 4;
        int b = a * a;  // should use inner `a`
    }
    int c = a * a;  // should use outer `a`
}"#);

test!(
    [snapshot]
    const_shadow = <ast::Block> r#"{
    const int a = 3;
    if (true) {
        const int a = 4;  // should be different from outer `a`
        int b = a * a;  // should use inner `a`
    }
    int c = a * a;  // should use outer `a`
}"#);

test!(
    [snapshot]
    const_shadows_outer_local = <ast::Block> r#"{
    int a = 3;
    if (true) {
        int b = a * a;  // should use inner `a`
        const int a = 4;
    }
}"#);

test!(
    [snapshot]
    local_shadows_outer_const = <ast::Block> r#"{
    const int a = 3;    // should be a_0
    if (true) {
        int b = a * a;  // should be a_0 * a_0
        int a = 4;      // should be a_1
        int c = a * a;  // should be a_1 * a_1
    }
}"#);

test!(
    [snapshot]
    local_disjoint = <ast::Block> r#"{
    if (true) {
        int a = 4;
        int b = a * a;  // should use inner `a`
    }
    if (true) {
        int a = 4;  // should be different from other inner `a`
        int b = a * a;  // should use new inner `a`
    }
}"#);

test!(
    [expect_fail("redefinition")]
    local_redefinition = <ast::Block> r#"{
    if (true) {
        int a = 4;
        int b = 3, a = 5;  // should fail on `a`
    }
}"#);

test!(
    [expect_fail("redefinition")]
    func_redefinition = <ast::Script> r#"
int foo(int x) {
    return x;
}

int foo(float y) {
    return y;
}
"#);

test!(
    [expect_fail("redefinition")]
    const_redefinition = <ast::Script> r#"
const int BLUE = 1;
const int RED = 3;
const int BLUE = RED;
"#);

test!(
    [expect_fail("redefinition")]
    func_scoped_redefinition = <ast::Block> r#"{
    if (true) {
        int foo(int x) {
            return x;
        }

        int foo(float y) {
            return y;
        }
    }
}"#);

test!(
    [expect_fail("redefinition")]
    const_scoped_redefinition = <ast::Block> r#"{
    if (true) {
        const int BLUE = 1;
        const int RED = 3;
        const int BLUE = RED;
    }
}"#);

test!(
    [snapshot]
    local_shadows_reg_alias = <ast::Block> r#"{
    ins_21(ALIAS, 3.0);
    if (true) {
        float ALIAS = 4.0;  // should be different `ALIAS`
        float b = ALIAS;
    }
    ins_21(ALIAS, 3.0);  // should be original `ALIAS`
}"#);

test!(
    [snapshot]
    func_scoped_shadows_ins_alias = <ast::Block> r#"{
    alias(4, 3.0);
    if (true) {
        void alias() {}  // should be different `alias`
        alias();
    }
    alias(4, 3.0);  // should be original `alias`
}"#);

test!(
    [all_names_unique]
    const_shadows_reg_alias = <ast::Script> r#"
const int A = ALIAS;
const int ALIAS = 3;
const int B = ALIAS;
"#);

test!(
    [all_names_unique]
    func_shadows_ins_alias = <ast::Script> r#"
void a() { alias(); }
void alias() {}
void b() { alias(); }
"#);

test!(
    [snapshot]
    separate_namespaces = <ast::Script> r#"
    const int a = a();           // should be a_0 then a_1
    const int a() { return a; }  // should be a_1 then a_0
"#);

// =========================================================================

#[should_panic(expected = "resolved multiple times")]
#[test]
fn panics_on_cloned_res() {
    let mut files = Files::new();
    let mut ctx = CompilerContext::new();
    ctx.extend_from_eclmap(None, &Eclmap::parse(ECLMAP).unwrap()).unwrap();

    let mut def = files.parse::<ast::Stmt>("<input>", b"  int x = 2;  ").unwrap();
    let mut cloned = files.parse::<ast::Stmt>("<input>", b"  x = 3;  ").unwrap();
    crate::passes::resolve_names::assign_res_ids(&mut def, &mut ctx).unwrap();
    crate::passes::resolve_names::assign_res_ids(&mut cloned, &mut ctx).unwrap();

    let block = ast::Block(vec![def, cloned.clone(), cloned]);

    crate::passes::resolve_names::run(&block, &mut ctx).unwrap();
}
