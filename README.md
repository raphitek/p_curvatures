# p_curvatures

In this project we provide the source code of the implementation in Sage of an algorithm computing the characteristic polynomials of the p-curvatures of a differential operator with coefficients in Z[x], for all p prime less than a given integer N, in quasi-linear time in N.

Files description and instructions : 
- p_curvature.sage is the main program
- p_curvature_verbose.sage is an alternative version of this program that let
  the user see the progression of the algorithm if he so wishes. It helps
  killing time when running on big operators, though it slows the execution
  a bit.
- test_3D_diagonal_queens_path.sage is a test file on a very large
  operator. As of yet I have not been able to run it to the end. Execute
  with the following instructions.
  """
    sage : %runfile p_curvature_verbose.sage
    sage : %runfile test_3D_diagonal_queens_path.sage
  """
- test_creative_telescoping.sage is a test file on operators of a certain
  type and of a more modest size. More operators of the same type can be
  found here : https://specfun.inria.fr/chyzak/ssw/ct-P.mpl and a study of
  those operators here :
  https://specfun.inria.fr/bostan/publications/BoChHoKaPe17.pdf . 
  Run with the following lines :
  """
    sage : %runfile p_curvature_verbose.sage
    sage : %runfile test_creative_telescoping.sage
  """
- test_p_curvetaure.sage is a test on two other operators linked with the
  Kreweras and Gessel walks. Run with the following lines
  """
    sage : %runfile p_curvature.sage
    sage : %runfile test_p_curvetaure.sage
  """
- explications_detaillées(fr).pdf is the memoire which explains how the
  algorithm works. It is in french, and a little outdated on specific
  points.

