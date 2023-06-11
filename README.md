This is a Python implementation of the Helfgott-Thompson algorithm for computing the Mertens function.

Their original C++ code is available at https://arxiv.org/abs/2101.08773.  The process of converting it to this code was roughly the following:

1.  Combine the four C++ files into a single file.
2.  Remove the pragmas that made it parallel.
3.  Translate it line-by-line directly into Python3.  There are some hiccups here related to pointer arithmetic and negative arguments in the division and remainder operations.
4.  In some cases where a function is invoked only once, inline that function.
5.  Make some further changes so that it plays more nicely with the interpreter, such as splitting the compound data types into multiple non-compound types.
