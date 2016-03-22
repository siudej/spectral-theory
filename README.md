# Explicit Laplace eigenvalues and variational tools

### `TrigInt.m`

The script contains a pattern matching based integration functions needed to speed up long trigonometric integrations. Such integrals occur in the variational approach to bounding Laplace eigenvalues on some special domains.

The same script also contains explicit formulas for eigenvalues and eigenfunctions on equilateral triangles, and rectangles.

Finally, many helper functions are also provided, e.g. Rayleigh quotient, function transplantations.

### `polyneg.m`

Implements an algorithm for proving symbolically that a polynomial in two variables is nonpositive on a given rectangle.

### Examples

These are used in some of the included Mathematica notebooks (see also their pdf printouts), and in many of my papers on Spectral Theory.

Other notebooks showcase different aspects of numerics used in spectral theory. Including an example of the meshless method of particular solutions leading to strict bounds for Laplace eigenvalues.
