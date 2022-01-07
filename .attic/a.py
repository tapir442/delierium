from delierium.JanetBasis import Janet_Basis
from delierium.MatrixOrder import Context, Mgrlex, Mgrevlex, Mlex
from IPython.core.debugger import set_trace

from System_2_24 import system_2_24, w, z,x,y
#%snakeviz
checkS=Janet_Basis(system_2_24,  (w, z), (x,y), Mlex)
checkS.show()

set_trace ()

#%load_ext snakeviz
#import time
from System_2_25 import system_2_25, w, z,x,y

#%snakeviz
checkS=Janet_Basis(system_2_25, (w, z), (x,y), Mlex)
checkS.show()

