<p align="center">
<a href="interop.md">Previous</a> |
<a href="index.md">Index</a> |
Next
</p>

# Preprocessor

TODO: This has changed a lot in the current compiler, this section needs revising.

Alogic implements a preprocessor which uses the syntax of the C preprocessor,
but has a significantly smaller feature set compared to the C preprocessor. The
main use of the preprocessor is to allow sharing of type definitions through
include files.

This section describes the available preprocessor directives.

### Include files

The `#include` directive can be used to include the contents of any source file
at the point where the directive is used. The relative path of the included file
must be specified in `" "` quotes. Any file can be included at any point, as
long as it makes sense to insert the entirity of that file at that point.

```
#include "interfaces.h" // the entirity of interfaces.h is inserted here

fsm a {
  in  sync a_t a;
  out sync b_t b;

  ...
}
```

### Text replacement macros

The `#define` directive can be used to define a macro that will undergo text
replacement by the preprocessor. Only simple macros are supported, not
function-like macros:

<a href="http://afiddle.argondesign.com/?example=preproc_macros.alogic">Fiddle with this macro here.</a>

```
#define MAGIC 4'd4
// at compile time, all instances of MAGIC will be replaced with the text "4'd4"

fsm magical {
    u4 a = MAGIC;
}
```

The use of `#define` macros is fairly limited, and their main purpose is to
share named constants between multiple entities. Within a single entity, the use
of `const` declarations is more appropriate.

### Conditional compilation

The preprocessor supports the `#if`, `#ifdef`, `#else` and `#endif` directives
to support a limited amount of conditional compilation, mainly aimed at
assisting with debugging by making debug statements conditional.

The use of `#if` and `#ifdef` is different in the Alogic preprocessor compared
to the C preprocessor in that both `#if` and `#ifdef` must be followed by the
name of a macro (i.e. `#if 0` is not valid).

`#ifdef MACRO_NAME` is true if the macro has been previously defined using
`#define`, or if it has been pre-defined on the compiler command line.

`#if MACRO_NAME` is only legal if the macro has been defined and evaluates to a
simple integer. It is then true if and only if the subject macro evaluates to a
non-zero value.

### Line control

Alogic supports the `#line` directive, which can be used to alter the file and
line information reported by the compiler. `#line` requires an integer argument
denoting the line number of the following line, and an optional string literal
denoting the file name to use for subsequent source code:

```
#line 10 "foo.alogic"
```

The line following the above directive will be processed as if it was line
10 of file `foo.alogic`. If the file name is omitted, the compiler continues
to use the current file name.

<p align="center">
<a href="interop.md">Previous</a> |
<a href="index.md">Index</a> |
Next
</p>
