# delierium
<b>D</b>ifferential <b>E</b>quations' <b>LIE</b> symmetries <b>R</b>esearch <b>I</b>nstr<b>UM</b>ent

Searching for symmetries in ODEs and PDEs using Python/SageMath.

# Status

still playing around with Janet bases

## Release 0.0.1.dev0

- Just constructing a Janet basis from a list of homogenuous linear PDEs (for grevlex and degrevlex order,
lex is dubious)


# Literature (and inspiration):
* Werner M. Seiler: Involution. The Formal Theory of Differential Equations and its Applications in Computer Algebra, Spinger Berlin 2010, ISBN 978-3-642-26135-0.
* Gerd Baumann: Symmetry Analysis of Differential Equations with Mathematica, Springer New York Berlin Heidelberg 2000, ISBN 0-387-98552-2.
* John Starrett: Solving differential equations by Symmetry Groups  (e.g https://www.researchgate.net/publication/233653257_Solving_Differential_Equations_by_Symmetry_Groups)
* Alexey A. Kasatkin, Aliya A. Gainetdinova: Symbolic and Numerical Methods for Searching Symmetries of Ordinary Differential Equations with a Small Parameter and Reducing Its Order, https://link.springer.com/chapter/10.1007%2F978-3-030-26831-2_19 (if you are able and willing to pay the 27 bucks)
* Vishwas Khare, M.G. Timol: New Algorithm In SageMath To Check Symmetry Of Ode Of First Order, https://www.researchgate.net/publication/338388495_New_Algorithm_In_SageMath_To_Check_Symmetry_Of_Ode_Of_First_Order
* Fritz Schwarz: Algorithmic Lie Theory for Solving Ordinary Differential Equations, CRC Press 2008, ISBN 978-1-58488-889-5
* Fritz Schwarz: Loewy Decomposition of Linear Differential Equations, Springer Wien 2012, ISBN 978-3-7091-1687-6

# Goals:

* Short term:
    * Play around and make some parts work (at least for the Q[x,y,z] domain), ready for a small 0.0.1 release
* Mid term:
    * Make it a valuable package
* Long term:
    * Maybe integration into SciPy|SymPy|SageMath



# Documentation

How to use:

>>> vars = var ("x y")
>>> z = function("z")(*vars)
>>> w = function("w")(*vars)
>>> f1 = diff(w, y) + x*diff(z,y)/(2*y*(x**2+y)) - w/y
>>> f2 = diff(z,x,y) + y*diff(w,y)/x + 2*y*diff(z, x)/x
>>> f3 = diff(w, x,y) - 2*x*diff(z, x,2)/y - x*diff(w,x)/y**2
>>> f4 = diff(w, x,y) + diff(z, x,y) + diff(w, y)/(2*y) - diff(w,x)/y + x* diff(z, y)/y - w/(2*y**2)
>>> f5 = diff(w,y,y) + diff(z,x,y) - diff(w, y)/y + w/(y**2)
>>> system_2_24 = [f1,f2,f3,f4,f5]
>>> checkS=Janet_Basis(system_2_24, (w,z), vars)
>>> checkS.show()
diff(z(x, y), y)
diff(z(x, y), x) + (1/2/y) * w(x, y)
diff(w(x, y), y) + (-1/y) * w(x, y)
diff(w(x, y), x)
