
# truth script syntax

All script languages implemented by truth share a common syntax (in fact, they are all parsed by *the same parser*).  This document is meant to serve as a primer on this script syntax.

**Disclaimer: This is by no means a complete specification of the language syntax.**

The grammar is similar to that of thecl.  It is generally C-like, with extensions for supplying additional metadata in the script file (such as image header data) or on instructions (such as time labels and difficulty masks).


## General features

### Base terminology

Things written at the outermost nesting level of a file are called **items**.

```C
entry {
    path: "subdir/file.png",
    has_data: false,
    sprites: {sprite0: {id: 0, x: 0.0, y: 0.0, w: 512.0, h: 480.0}},
}


script 0 script0 {
    anchor(1, 2);
    int i = RAND % 2;
    if (i == 1) {
        pos(0.0, 2.0, 0.0);
    }
}
```

This ANM script file above has two items, an `entry` "meta" item and a `script`.

Inside the script are a number of **statements**.  Those statements may contain **blocks**, **literals** (`1`, `0.0`), **variables** (`i`, `RAND`), and other **expressions** (`RAND % 2`).

### Literals

Literals can be:

* **Integers:** `123`, `0x123`, `-0b00101`, `true`, `false`.  There is no octal syntax. Literal numbers have no optional leading plus.
* **Floats:** `1.0`, `-1.3f`, `2f`.  Again, no leading plus.
* **Strings:** `"The quick brown fox\njumped over the lazy dog"`.  The control characters for strings are `\0`, `\n`, `\r`, `\\`, and `\"`.  

In the game's own files, strings are encoded in Shift-JIS, though thcrap also lets them be in UTF-8.  Currently, `truth` dumps the string bytes back and forth identically except for escaping, without any regard to encoding.  In theory, this can lead to... [problems](https://github.com/ExpHP/truth/issues/2), which may be addressed in later versions.

### Variables

The touhou games provide ECL and ANM with a fixed number of **registers** (which are either integers or floats).  truth names these `REG[<n>]`, where `<n>` is an integer identifying the register.  E.g. in ANM, `REG[10022]` is the register that draws a random integer.

The games allow most registers can be read either as integers or floats.  You can choose which type to use a register as by supplying a **type sigil**: `$` for integers or `%` for floats.

```C
$REG[10000] = $REG[10022] % 3;
%REG[10004] *= 0.5;
```

Most registers have a fixed type that they are stored as in the game's memory (known as the register's "inherent type"), and truth is by default configured with knowledge of all of these inherent types for all registers in each game.  If you supply no sigil, truth will default to the register's inherent type. E.g. `REG[10001]` in ANM is an integer, while `REG[10004]` is a float.  When you read a variable as the wrong type, the game will *usually* perform a type-cast.

Registers can be given aliases via a mapfile (see the [main readme](https://github.com/ExpHP/truth#readme)).  This allows you to use identifiers instead:

```C
I0 = RAND % 3;
F0 *= F0;
```

**Locals** are variables with a limited lexical scope.  These have to be declared, with syntax like in C:

```C
int i = 0;
int j;
float x = 3.0, y, z = F0;   // note: y here is uninitialized
var w;   // <-- untyped; only permitted in languages with a stack
```

In modern ECL, these will use the stack.  In early ECL and ANM, they will be automatically assigned general-purpose registers.  In both, they are scoped to their containing block.

Similar to registers, you can apply type sigils to locals.  (in fact, all kinds of variables support type sigils)

```C
I0 = $F0;  // performs a truncating cast
```

**Consts** are compile-time constant variables.  Unlike local declarations (which are statements), `const` declarations are technically considered a form of item.  This means they can be accessed from *anywhere* within the same block (even before the declaration).

```
const int before = 3;
const int middle = after * before;
const int after = 5;
```

Unlike locals, `const` vars muse be initialized.

Something interesting to note: While the other kinds of variables are limited to integers and floats, `const` vars may also be strings!

```
const string FIRST_NAME = "Johnny";
```

### Instructions

A call to a raw instruction looks like this.  The part after `ins_` is the opcode, which must be written in a canonical form (no leading zeroes!):

```C
ins_420(69, I0);
```

**All identifiers beginning with `ins_` are reserved for this purpose.** Much like thtk, mapfiles can also give names to instructions:

```C
seti(23, I0);
```

In this case, raw instructions are basically indistinguishable from any other function calls of void type. ....At least, that's what I would say, but *function calls beyond singular instructions are not yet implemented.*

(at some point, inline functions like thecl will be a thing! And truecl will likely share thecl's sugar for invoking other subroutines without the `call` instruction)

### Expressions

The following binary operations are recognized: `+`, `-`, `*`, `/`, `%`, `&`, `^`, `|`, `&&`, `||`, `==`, `!=`, `<`, `<=`, `>`, `>=`.  They have the same levels of precedence as in C.  

All operators are implemented in all languages *where possible*.  For instance, in ANM, it may be possible to use the bitwise or operator `|` in compile-time constant expressions, but not in other places (as ANM provides no instructions for bitwise operators).

Other things present in expressions:

* The **ternary operator** `a ? b : c`.  Right associative, [the way it should be](https://eev.ee/blog/2012/04/09/php-a-fractal-of-bad-design/#operators).
* **Unary negation** `-x`.
* **Special functions** `sin(x)` and `cos(x)`.
* **Explicit casts** `_S` (float to int) and `_f` (int to float): `I0 = _S(F0);`
  * That example is identical to `I0 = $F0`, but `_S` is also more generally usable in larger expressions where it may introduce a temporary 

### Assignments

Unlike in C, assignments are **not** expressions; they are statements.  They are anything of the form

```C
<var> = <expr>;
<var> += <expr>;
<var> -= <expr>;
...
```
...and so on for each of `*=`, `/=`, `%=`, `&=`, `|=`

(**note:** it's possible that in the future I might consider turning assignments into expressions, as a generalization of "clobber" syntax)

### Block structures

`if`/`while` require parentheses around their conditions, and also require braces around their statements.

```C
if (I0 == 1) {
    do_a_thing();
} else if (I0 == 2) {
    do_another_thing();
} else {
    do_a_third_thing();
}
```

There are also a number of looping constructs:

```C
loop {
    freddy();
}

float x = 0.1f;
do {
    x += 0.5;
    fazbear(x);
} while (x < 3f);

while (x < 3f) {
    is_watching();
}

times(I0) {
    you();
}
```

The last one is sugar for the following:

```C
// note: in reality the compiler generates an anonymous
//       temporary whose scope ends after the block
int temp = I0;
while (--temp) {
    you();
}
```

In languages without a stack, this temporary `temp` will use up one of your precious integer scratch registers.  If you would like it to reuse a register that you're already using, you can provide a variable to use as a **clobber**:

```C
// this will use I2 instead of creating a temporary.
times(I2 = I0) {
    you();
}
```

#### About conditions
 
In the desugared form of `times()` above, you'll notice that there is a `while (--var)`.  This `--var` is not an expression!

Basically, a **condition** can either be an expression `<expr>` or a predecrement operation `--<var>`.  The latter compiles to a special kind of jump available in ANM and early ECL that decrements a variable and jumps if it is nonzero.  (*every single `while` loop in vanilla ANM files uses this form of jump,* so the ability to decompile it seemed... kind of important!)

### Time labels

In all of Touhou's scripting languages, every instruction comes with a property known as its "time label."  This is used to schedule execution of instructions.

Accordingly, truth assigns a time label to every *statement* (even those that do not produce any instructions).  Normally each statement copies the time label from the previous one, but you can modify the time label by writing one of the following:

* `40:` is an **absolute time label**, setting the time label to 40.
* `+40:` is a **relative time label**, increasing the time label by 40.
* `-40:`, to be clear, is an absolute time label, setting it to `-40:`.  (you'll frequently see `-1:` at the end of early STD scripts!)

```C
script script0 {
    test();   // has time label 0
30:
    test2();  // has time label 30
    test3();  // has time label 30
+27:
    test4();  // has time label 57
-10:
    test5();  // has time label -10
}
```

Placing a relative time label at the beginning or end of a block is always supported in `truth`, and will do what you would intuitively expect:

```C
loop {
+4:
    foo();
+6:
}
```

This example will call `foo()` on frames 4, 14, 24, 34, etc.

### Conditional jumps and labels

The control flow structures desugar like this:

```C
15:
    if (I0 == 0) {
        funny();
    } else {
        happy();
    }

// desugars into
15:
    if (I0 != 0) goto else_label;
    funny()
    goto end_label;
else_label:
    happy();
end_label:
```

Here you see the syntax for raw jumps and labels.

* `else_label:` is a label (local to that function; no jumping between functions!).
* `goto end_label;` jumps to `end_label` and sets the current time to `end_label`'s time label.
* `if (I0 != 0) goto else_label;` is a raw conditional jump.

Notice that, unlike conditional blocks, *the conditional jump has no braces*; it is a special syntactic construct.

```C
// this compiles to a single instruction in anm
if (I0 != 0) goto else_label;
 
// this typically compiles to more than one instruction
if (I0 != 0) {
    goto else_label;
}
```

The `goto label` also has a more explicit form which mentions the time to set as the current time:

```C
    if (I0 != 0) goto else_label @ 15;
    funny()
    goto end_label @ 15;
else_label:
    happy();
end_label:
```

However, this is generally obsolete.  Normally, the only reason the game ever uses this feature is to set the time equal to the instruction before the jump target.  However, in `truth`, labels have their own time labels, so this can be accomplished simply by moving the label:

```C
10:
    foo()
+5:
label:  // has time label 15
    bar()
    goto label @ 10;
    

// is equivalent to
10:
    foo()
label:  // has time label 10
+5:
    bar()
    goto label;    // <-- no explicit time necessary
```

One final thing:  You may have noticed that the desugaring of `if (...) { ... }` into `if (...) goto label` requires negating the condition.  But what if the condition can't be negated? (an example of this occurs with `--var`)

For this reason, there also exists **the `unless` keyword** for writing a negated `if`:

```C
unless (var--) {
    boo();
}
```

*__Note:__ The `unless` keyword may eventually be removed.  Currently it's only present to make the implementation easier, and you are generally discouraged from using it.*


## Metadata

Things like ANM entry headers and STD file headers are written using **meta** items.  These look like similar to JSON5-like syntax:

```C
meta {
    unknown: 0,
    stage_name: "dm",
    bgm: [
        {path: "bgm/th08_08.mid", name: "dm"},
        {path: "bgm/th08_09.mid", name: "dm"},
        {path: " ", name: " "},
        {path: " ", name: " "},
    ],
    objects: {
        object0: {
            unknown: 1,
            pos: [-81.602196, -140.91132, -425.6022],
            size: [531.2044, 505.268, 571.2044],
            quads: [
                rect {anm_script: 2, pos: [64.0, 224.0, -64.0], size: [112.0, 96.0]},
                rect {anm_script: 2, pos: [234.0, 224.0, -202.0], size: [-112.0, 96.0]},
            ],
        },
    },
    instances: [object0 {pos: [-192.0, 6600.0, 0.0]}],
}
```

The building blocks you see here are:

  * String, integer, and float literals. (as [specified above](#literals))
  * Arrays: `[64.0, 224.0, -64.0]`.
  * Objects: `{path: " ", name: " "}`.
    * The keys are *always* identifiers. (no quoted keys).
    * These are ordered maps.  I.e. rearranging the order of key-value pairs *can* change compilation output, but only for certain things (e.g. fields of the `objects: {...}` object above).
  * Variants: `object0 {pos: [-192.0, 6600.0, 0.0]}`
    * This is just an object with another identifier in front of it.  This identifier may have an effect on what fields the object is expected to contain.  E.g. instead of `rect { ... }` with `anm_script, pos, size` there is also `strip { ... }` with `anm_script, start, end, width`.


## Reserved syntax

Some forms of syntax are parsed simply to reserve them for future use (and to ensure that they remain unambiguous in the grammar).  They will likely end up having similar meaning in truth to their existing meanings in thecl:

* `return;` and `return <expr>;`
* `int foo(int x) { ... }` function definition.
* `int foo(int x);` function declaration.
* `@foo(a, b, c);` explicit sub call sugar.
* `foo(a, b, c) async;` call-async sugar.
