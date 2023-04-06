


# this is the starnge paper with interaction 
# Program for finding determining equationfor PDE OF ORDER ONE TWO AND THREE
print("""program find determining equ of the type u_i = f(u_k , u , x , t) where i, k
can take value x, t ,tt, xx, xt, xxx,
xxt, xtt, ttt and u_i is not equal to
u_k""")
var("x, t, u, u_x, u_t, u_xx, u_xt, u_tx,u_tt, u_xxx , u_xxt , u_xtt , u_ttt , u_ttx ,u_txx, c , a")
function("X, Y, f , F , U, T , V, w")
# Define function
import itertools
@interact
def partialsymmetry(A= input_box(default = u_xxx, label = "Insert u_i " ) ,
                    w = input_box(default = u_t * u * u_x , label = "Insert f of eq u_i = f(u_j, u, x, t )")) :
    W=A (w)
# 1)
D_xU= diff(U(x ,t ,u), x) + \
    u_x * diff(U(x, t ,u), u) + \
    (u_xx * diff(U(x, t, u), u_x) + u_xt * diff(U(x, t, u), u_t )) + \
    (u_xxx * diff(U(x, t, u), u_xx) + u_xxt * diff(U(x, t , u), u_xt) + u_xtt * diff(U(x, t, u), u_tt))

D_tU = diff(U(x, t, u), t) + \
    u_t * diff(U(x, t, u), u) + \
    (u_tt * diff(U(x, t, u), u_t) + u_xt * diff(U(x, t, u), u_x)) + \
    (u_ttt * diff(U(x, t, u), u_tt) + u_xtt * diff(U(x, t, u), u_xt) + u_xxt * diff(U(x, t, u), u_xx))
# 2)
D_xT= diff(T(x, t, u), x) + \
    u_x * diff(T(x, t, u), u) + \
    (u_xx * diff(T(x, t, u), u_x) + u_xt * diff(T(x, t, u), u_t)) + \
    (u_xxx * diff(T(x, t, u), u_xx) + u_xxt * diff(T(x, t, u), u_xt) + u_xtt * diff(T(x, t, u), u_tt))

D_tT = diff(T(x, t , u), t) + \
    u_t * diff(T(x, t, u), u) + \
    (u_tt * diff(T(x, t, u), u_t) + u_xt * diff(T(x, t, u), u_x)) + \
    (u_ttt * diff(T(x, t, u), u_tt) + u_xtt * diff(T(x, t, u), u_xt)+ u_xxt * diff(T(x, t, u), u_xx))
# 3)
D_xX= diff(X(x, t, u), x) + \
    u_x * diff(X(x, t, u), u) + \
    (u_xx * diff(X(x, t, u), u_x) + u_xt * diff(X(x, t, u), u_t)) + \
    (u_xxx * diff(X(x, t, u) , u_xx) + u_xxt * diff(X(x, t, u), u_xt) + u_xtt * diff(X(x, t, u), u_tt))

D_tX= diff(X(x, t, u), t) + \
    u_t * diff(X(x, t, u), u) + \
    (u_tt * diff(X(x, t, u), u_t) + u_xt * diff(X(x, t, u), u_x)) + \
    (u_ttt * diff(X(x, t, u), u_tt) + u_xtt * diff(X(x , t, u) , u_xt) + u_xxt * diff(X(x, t, u), u_xx))

# A ) ( For first order pde )
U_x = D_xU * u_t *D_xT * u_x *D_xX
print("Value of u_x is ")
show(u_x)
# B)
u_t =D_tU * u_t * D_tT * u_x * D_tX
print("Value of u_t is")
show (u_t)
# 4 ) ( F o r s e c o n d o r d e r pde )
D_xUx = diff(U_x, x) + \
    u_x * diff(U_x, u) \
    + (u_xx * diff(U_x, u_x) + u_xt * diff(U_x, u_t))  \
    + (u_xxx * diff(U_x, u_xx) + u_xxt * diff(U_x, u_xt) + u_xtt * diff(U_x, u_tt ))


D_tUt = diff(u_t, t) \
    + u_t * diff(u_t, u) \
    + (u_tt * diff(u_t, u_t) + u_xt * diff(u_t, u_x)) \
    + (u_ttt * diff(u_t, u_tt)+ u_xtt * diff(u_t, u_xt) + u_xxt * diff(u_t, u_xx))

D_xUt = diff(u_t, x) \
    + u_x * diff(u_t, u) \
    + (u_xx * diff(u_t, u_x) + u_xt * diff(u_t, u_t)) \
    + (u_xxx * diff(u_t, u_xx) + u_xxt * diff(u_t, u_xt) + u_xtt * diff(u_t , u_tt ))

# A ) ( F o r s e c o n d o r d e r pde )
u_xx = D_xUx * u_xt *D_xT * u_xx *D_xX
print("Value of u_xx is")
show(u_xx)
# B)
u_tt = D_tUt * u_tt * D_tT * u_xt * D_tX
print("Value of u_tt is")
show(u_tt)
# C)
u_xt = D_xUt * u_tt * D_xT * u_xt * D_xX
print("Value of u_xt is")
show(u_xt)
# 5 ) ( F o r t h i r d o r d e r pde )
D_xUxx = diff(u_xx, x) \
    + u_x * diff(u_xx, u) \
    + (u_xx * diff(u_xx, u_x) + u_xt * diff(u_xx, u_t)) \
    + (u_xxx * diff(u_xx, u_xx) + u_xxt * diff(u_xx, u_xt) + u_xtt * diff(u_xx, u_tt))

D_tUtt = diff(u_tt, t) \
    + u_t * diff(u_tt, u) \
    + (u_tt * diff(u_tt, u_t) + u_xt * diff(u_tt, u_x)) \
    + (u_ttt * diff(u_tt, u_tt) + u_xtt * diff(u_tt, u_xt) + u_xxt * diff(u_tt, u_xx))

D_xUxt = diff(u_xt, x) \
    + u_x * diff(u_xt, u) \
    + (u_xx * diff(u_xt, u_x) + u_xt * diff(u_xt, u_t)) \
    + (u_xxx * diff(u_xt, u_xx) + u_xxt * diff(u_xt, u_xt) + u_xtt * diff(u_xt, u_tt))

D_tUxt = diff(u_xt, t) \
    + u_t * diff(u_xt, u) \
    + (u_tt * diff(u_xt, u_t) + u_xt * diff(u_xt, u_x)) \
    + (u_ttt * diff(u_tt, u_tt) + u_xtt * diff(u_xt, u_xt) + u_xxt * diff(u_xt, u_xx))

# A) ( F o r t h i r d o r d e r pde )
u_xxx = D_xUxx * u_xxt * D_xT * u_xxx * D_xX
u_ttt = D_tUtt * u_ttt * D_tT * u_xtt * D_tX
u_xxt = D_xUxt * u_xtt * D_xT * u_xxt *D_xX
u_xtt = D_tUxt * u_xtt * D_tT * u_xxt * D_tX
#
X2 = X(x, t, u) * diff(W, x) + \
    T(x, t, u) * diff(W, t) + \
    U(x, t, u) * diff(W, u) + \
    (u_x) * diff(W, u_x) + \
    (u_t) * diff(W, u_t) + \
    (u_xx) * diff(W, u_xx) + \
    (u_xt) * diff(W, u_xt) + \
    (u_tt) * diff(W, u_tt) + \
    ((u_xxx) * diff(W, u_xxx) + \
     (u_xxt) * diff(W, u_xxt) + \
     (u_xtt) * diff(W, u_xtt) + \
     (u_ttt) * diff(W, u_ttt))
# print( ” The v a l u e o f X2 i s ” )
# show ( X2==0)
if (A == u_x):
    K = X2 (u_x = w).simplify_full()
elif (A == u_t):
    K = X2 (u_t = w).simplify_full()
elif (A == u_xx):
    K = X2 (u_xx = w).simplify_full()
elif (A == u_xt ) :
    K = X2 (u_xt =w ).simplify_full ()
elif (A == u_tt ) :
    K = X2 (u_tt =w ).simplify_full ()
elif (A == u_xxx ) :
    K = X2 (u_xxx =w ).simplify_full ()
elif (A == u_xxt ) :
    K = X2 (u_xt = w).simplify_full ()
elif (A == u_xtt ) :
    K = X2 (u_xtt = w).simplify_full ()
elif (A == u_ttt ) :
    K = X2 (u_ttt = w).simplifyfull ( )
K= (numerator(K ) )
# show (K.coefficient ( u_x**3 ) )
# print( ” The v a l u e o f K i s ” )
# show (K==0)
print("The determining equations are given by ")
F = [1 ,2 ,3 ,4]
E = [1 ,2]
L = [u_x, u_t, u_xx, u_xt, u_tt, u_xxx, u_xxt, u_xtt, u_ttt]
I = []
J = []
v = []
for i , j , k in itertools.product(L, L, L):
    if i != j and j != k :
        for a , b , c in itertools.product (F, F, F) :
            s = i**a * j**b *k**c
            e = i**a * j**b
            d = i**a
            I.append (s)
            J.append (e)
            v.append (d)
    for m in I :
        if ((K.coefficient (m ) ) != 0) :
            # print( ” The coefficient o f,m, ” i s ” )
            show (K.coefficient (m) == 0)
            K= (K(K.coefficient (m) *m)).simplify_full ()
    for m in J :
        if ((K.coefficient (m)) != 0):
            # print( ” The coefficient o f,m, ” i s ” )
            show (K.coefficient (m) == 0 )
            K= (K(K.coefficient (m) *m) ).simplify_full()
    for m in v :
        if ((K.coefficient (m)) != 0) :
            # print( ” The coefficient o f,m, ” i s ” )
            show (K.coefficient (m) == 0 )
            K= (K(K.coefficient(m)*m)).simplify_full()
            # print( ” The coefficient o f u_x ˆ0” ,” is ”)
            show (K==0)
