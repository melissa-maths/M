####################################################################################
####################################################################################
###
### Python code accompanying the paper
###    'Maximal subgroups of the Monster group'
### by Dietrich, Lee, Popiel (2023)
###
### Code relies in Python package mmgroup by Martin Seysen
### https://github.com/Martin-Seysen/mmgroup
###
###
### Main results are the following:
###  * Standard generators for G = 2^(1+24).Co1, see SECTION 1
###  * Generators for new maximal PGL(2,13), see SECTION 2
###  * Computations assisting the proofs in the paper, see SECTION 3
###
####################################################################################
####################################################################################


from mmgroup import *
import random
import itertools as it
import numpy as np
from functools import reduce


####################################################################################
####################################################################################
####################################################################################
### SECTION 1
###
### standard generators for G = 2^(1+24).Co1
###
### call verify_std_gens_G(a,b) to verify correctness
###
a = MM("M<y_2feh*x_51h*d_6f2h*p_199553794*l_2*p_1900800*l_2*p_684120>")
b = MM("M<y_32bh*x_0e4h*d_30fh*p_81928987*l_2*p_2880*l_1*p_21312*l_1*p_10455360>")
###
####################################################################################


####################################################################################
### verify that a and b generated G
###

### define group commutator [a,b] = a^{-1} * b^{-1} * a * b
def Comm(a,b):
   return a**(-1)*b**(-1)*a*b


### various check to confirm that a and b have the claimed properties
def verify_std_gens_G(a,b):
   #check central element
   cent = MM("M<x_1000h>")
   if not (Comm(a**2,b**3) == cent and a*cent == cent*a and b*cent == cent*b):
       return False
   #check membership in G_x0
   c0 = a.in_G_x0() and b.in_G_x0()
   #check right orders
   c1 = a.order()==4 and b.order()==6
   #check belong to right classes of G_x0
   c2 = a.chi_G_x0()[1]==-13 and b.chi_G_x0()[1]==2 and (b.chi_G_x0()[0]==-3 or b.chi_G_x0()[0]==5)
   #check product in right class
   c3 = (a*b).order()==40 and ((a*b)**-1).chi_G_x0()[1]==0 and ((a*b)**-1).chi_G_x0()[2]*((a*b)**-1).chi_G_x0()[3]==0
   #check that elt powers are not central in subgroup generated by a and b
   c4 = (a**2)*b != b*(a**2) and (b**2)*a != a*(b**2) and (b**3)*a != a*(b**3)
   #check that a*b*a*(b^2) has order 6 in quotient - choices are 6 or 21 so if latter, evaluates to false
   c5 = (a*b*a*b**2).order() % 6 ==0
   if not (c0 and c1 and c2 and c3 and c4 and c5):
       return False
   #now check that we can generate Q: construct j0,..,j23
   myels = [(a**2)**((a*b)**i) for i in range(0,24)]
   #elts need to lie in Q, commute modulo cent, and should have order 2
   for i in range(0,24):
       if not myels[i].in_Q_x0():
           return False
       for j in range(i+1,24):
           if (myels[i]*myels[j] != myels[j]*myels[i]) and Comm(myels[i],myels[j]) != cent:
               return False
           if myels[i].order() != 2:
               return False
   print("all good so far; now check size of Q;")
   print("this will take a long time")
   #check that ((myels[0]**i0)* ... *(myels[23]**i23)).order() == 1 mod <cent> only for i0==...==i23=0
   s=0
   tups = it.product([0,1], repeat=24)
   for t in tups:
       if np.sum(t)==0:
           continue
       if s % 10000 == 0:
           print("Done ", s, " of ",2**24," tuples: ",100*s/2**24,"%", end='\r')
       terms = [myels[i]**t[i] for i in range(24)]
       prod = reduce((lambda x, y: x * y), terms)
       if prod.order() ==1 or (prod*cent).order()==1:
           print("Found identity with tuple: ", t)
           return False
       s+=1
   print("all tests ok")
   return True


### verify_std_gens_G(a,b) returns true

####################################################################################

### the homomorphism G --> GL_2(24) whose image is a 24-dim Z_2 rep of Co1
def elt_to_24_mat(g):
   mat = []
   for i in range(24):
       x = generators.gen_leech2_op_word_leech2(2**(23-i),g.mmdata,len(g.mmdata),0)
       mat.append([int(d) for d in format( (x %2**24), '#026b')[2:]])
   return mat

####################################################################################

### MAGMA: The following Magma code confirms that <A,B> generate Co1;
### below A and B are the two matrices in GL(24,2) that have been computed 
### via elt_to_24_mat(a) and elt_to_24_mat(b)
###
###   A := GL(24, GF(2)) ! Matrix(GF(2), 24, 24, \[ 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
###   0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1,
###   0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
###   0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
###   0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0,
###   1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0,
###   0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1,
###   0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1,
###   1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1,
###   0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0,
###   0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0,
###   0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1,
###   0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1,
###   1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0
###   ]);
###   B := GL(24, GF(2)) ! Matrix(GF(2), 24, 24, \[ 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
###   1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1,
###   1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1,
###   0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
###   1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1,
###   1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
###   0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0,
###   0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1,
###   0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1,
###   0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
###   0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1,
###   1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1,
###   0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1,
###   0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1
###   ]);
###
###   G := sub<GL(24,2)|[A,B]>;
###   LMGCompositionFactors(G);
###   // Output: G -- Co1 -- 1
###
####################################################################################
###
### In conclusion:
### The latter proves that the images of {a,b} in GL(24,2) generate Co1.
### Above we have also seen that we can use {a,b} to generate Q
### All elements lie in G, so it follows that G = <a,b>







####################################################################################
####################################################################################
####################################################################################
### SECTION 2
### Generators of L = PGL(2,13) = <g13, g6, i2, a12>,
### where g13, g6, i2, a12 have orders 13, 6, 2, 12.
###
### We have PSL(2,13) = <g13, g6, i2> with <g13,g6> = 13:6 and <g6,i2> = D12
###
g13 = MM("M<y_519h*x_0cb8h*d_3abh*p_178084032*l_2*p_2344320*l_2*p_471482*l_1*t_1*l_2*p_2830080*l_2*p_22371347*l_2*t_2*l_1*p_1499520*l_2*p_22779365*l_2*t_1*l_2*p_2597760*l_1*p_11179396*t_1*l_1*p_1499520*l_2*p_85838017*t_2*l_1*p_1499520*l_1*p_64024721*t_2*l_2*p_2386560*l_2*p_21335269>")

g6 = MM("M<y_764h*x_590h*d_0bf6h*p_63465756*l_1*p_24000*l_2*p_528432*t_1*l_2*p_1457280*l_1*p_23214136*l_1*t_2*l_2*p_2344320*l_2*p_13038217*l_2*t_1*l_2*p_2956800*l_1*p_85332887*t_2*l_2*p_2830080*l_2*p_85335745*t_2*l_2*p_1900800*l_2*p_13472*t_2*l_2*p_2386560*l_2*p_85413728*t_1*l_2*p_2386560*l_2*p_53803593>")

i2 = MM("M<y_6ch*x_7ch*d_52ah*p_115885662*l_2*p_2787840*l_2*p_12552610*l_2*t_1*l_2*p_1900800*l_2*p_31998118*l_2*t_2*l_2*p_80762880*l_1*p_243091248*l_2*t_1*l_2*p_2597760*l_1*p_42794439*t_1*l_1*p_1394880*l_2*p_64015152*t_1*l_1*p_2027520*l_1*p_177984*t_1*l_2*p_79432320*l_1*p_161927136>")

a12 = MM("M<y_1afh*x_1661h*d_2ddh*p_208095583*l_2*p_1943040*l_2*p_1974295*l_2*t_2*l_2*p_1900800*l_2*p_10778*l_2*t_2*l_2*p_1900800*l_2*p_1868387*l_1*t_1*l_2*p_2956800*l_1*p_11159238*t_1*l_2*p_1985280*l_1*p_86275805*t_2*l_2*p_2386560*l_2*p_42712609*t_2*l_1*p_1499520*l_1*p_106699812>")
####################################################################################
####################################################################################


####################################################################################
###
### verify that g13, g6, i2, a12  generated PGL(2,13)
### use presentation of PGL(2,13) provided by Corollary 4 in 
###    Robertson and Williams
###    'A presentation of PGL(2,p) with three defining relations'
###    Proc. Edinb. Math. Soc. 27 (145-149 1994)
###
### various check to confirm that a and b have the claimed properties
def verify_gens_PGL2_13(g13,g6,i2,a12):
  u = (i2*g6**4)*a12
  v = g13
  rels = [u**2,v**13,(u*(v**2))**4,(u*v*u*(v**2))**3]
  for i in rels:
     if not i.order() == 1:
        return False
  if not (g13.order() == 13 and g6.order() == 6 and i2.order() == 2 and a12.order() == 12):
        return False
  return True


## verify_gens_PGL2_13(g13,g6,i2,a12) returns true

####################################################################################
####################################################################################
####################################################################################
### SECTION 3
###
### Computation used in the proof of Corollary 3.3:
### We have g6=y*t and need to show that the only element in <t> fixed by i2 is t^0
###
y = MM("M<y_4fh*x_1331h*d_0d46h*p_79853974*l_2*p_1943040*l_2*p_2398522*t_1*l_2*p_2344320*l_2*p_1858757*l_2*t_1*l_1*p_960*l_2*p_3120*l_2*p_517440*t_2*l_2*p_2597760*l_1*p_12132032*t_2*l_2*p_2880*l_1*p_465840*l_1*p_1565760*t_1*l_2*p_960*l_1*p_63994992*t_1*l_1*p_2027520*l_1*p_50146>")
t = MM("M<y_44eh*x_1906h*d_2d9h*p_173881751*l_1*p_2640000*l_1*p_1925314*l_1*t_1*l_1*p_2999040*l_1*p_2392772*l_1*t_1*l_1*p_1499520*l_1*p_32461673*l_1*t_1*l_2*p_2344320*l_2*p_84794*t_2*l_2*p_2956800*l_1*p_85413707*t_2*l_2*p_1985280*l_1*p_96477721*t_1*l_2*p_1985280*l_1*p_64023741>")

###Verify that g6 = y*t, and that the only elt of <t> that is fixed by i2 is the identity
def verify_cent_PGL2_13(g6,y,t,i2):
  return g6==y*t and [t**i for i in range(6) if (t**i)**i2==t**i] == [MM("M<1>")]

####################################################################################
### The representatives of the 5 conjugacy classes of 13:6s 
### Element of order 13 is g13 above.
### First rep is the same y defined above - this lies in 6B
###
y = MM("M<y_4fh*x_1331h*d_0d46h*p_79853974*l_2*p_1943040*l_2*p_2398522*t_1*l_2*p_2344320*l_2*p_1858757*l_2*t_1*l_1*p_960*l_2*p_3120*l_2*p_517440*t_2*l_2*p_2597760*l_1*p_12132032*t_2*l_2*p_2880*l_1*p_465840*l_1*p_1565760*t_1*l_2*p_960*l_1*p_63994992*t_1*l_1*p_2027520*l_1*p_50146>")

### 6F case
yd = MM("M<y_8ah*x_1b2ch*d_0b85h*p_161672761*l_1*p_1499520*l_1*p_32571364*l_2*t_2*l_2*p_2956800*l_1*p_33438307*l_1*t_2*l_1*p_1393920*l_1*p_2160*l_2*p_4331520*t_1*l_2*p_2956800*l_1*p_11152592*t_1*l_2*p_1858560*l_2*p_2208*l_1*p_2028480*t_1*l_1*p_21120*l_2*p_96477744*t_1*l_2*p_1943040*l_2*p_42730017>")

###The three 6E reps
yt_1 = y*t
yt_2 = y*t**2
yt_3 = y*t**3

### Should be all 6s
[y.order(), yd.order(), yt_1.order(), yt_2.order(), yt_3.order()]

###Centraliser generators
yd_normaliser_gens = [MM("M<y_4e9h*x_1d58h*d_193h*p_241042748*l_2*p_2956800*l_1*p_13036314*l_2*t_1*l_2*p_1457280*l_1*p_12059861*l_2*t_1*l_2*p_960*l_1*p_2160*l_1*p_536640*t_1*l_2*p_2386560*l_2*p_53376357*t_2*l_2*p_1920*l_2*p_22320*l_2*p_2093760*t_2*l_1*p_1499520*l_1*p_64006449*t_2*l_2*p_2956800*l_1*p_96484459>"),
MM("M<y_585h*x_0b11h*d_1d8h*p_42155487*l_2*p_1943040*l_2*p_31997952*l_1*t_1*l_1*p_466560*l_2*p_21797088*l_1*t_2*l_2*p_2956800*l_1*p_21886690*l_1*t_2*l_1*p_2640000*l_1*p_11541*t_2*l_2*p_1985280*l_1*p_42754979*t_1*l_1*p_1394880*l_2*p_465792*l_1*p_10330560*t_2*l_2*p_2880*l_2*p_43170912*t_1*l_1*p_2328000>"),
MM("M<y_146h*x_4bch*d_50dh*p_24985824*l_2*p_2386560*l_2*p_474466*t_1*l_1*p_2027520*l_1*p_21891472*l_2*t_2*l_2*p_1394880*l_2*p_1152*l_1*p_1946880*t_2*l_2*p_2597760*l_1*p_42664551*t_2*l_2*p_1943040*l_2*p_96040869*t_1*l_1*p_1499520*l_2*p_21442962*t_2*l_2*p_5684160*l_1>"),
MM("M<y_0eh*x_769h*d_90fh*p_156330167*l_1*p_2640000*l_1*p_11707800*t_2*l_1*p_23040*l_2*p_12545616*l_1*t_1*l_1*p_2640000*l_1*p_13036312*l_1*t_1*l_2*p_2597760*l_1*p_42676071*t_1*l_1*p_1436160*l_1*t_1*l_2*p_1858560*l_1*p_467856*l_2*p_6551040*t_2*l_2*p_2597760*l_1*p_96033226*t_1*l_2*p_1943040*l_2*p_85411777>"),
MM("M<y_21h*x_0e96h*d_0e27h*p_91470589*l_2*p_1985280*l_1*p_22400*l_2*t_2*l_1*p_1394880*l_2*p_23328*l_2*t_1*l_1*p_2999040*l_1*p_1931027*l_1*t_1*l_2*p_2344320*l_2*p_9602*t_1*l_2*p_2386560*l_2*p_53842003*t_2*l_2*p_2344320*l_2*p_256933*t_1*l_1*p_1499520*l_2*p_96462321*t_1*l_2*p_1985280*l_1*p_85820722>"),
MM("M<y_5ceh*x_1a4ah*d_0a41h*p_211770336*l_2*p_2787840*l_2*p_11672165*l_1*t_2*l_1*p_2027520*l_1*p_11601779*l_1*t_2*l_2*p_1943040*l_2*p_33019747*l_1*t_1*l_2*p_1985280*l_1*p_42675090*t_1*l_2*p_2386560*l_2*p_85417569*t_1*l_2*p_1985280*l_1*p_482049*l_1*t_1*l_2*p_1943040*l_2*p_96018819*t_1*l_2*p_2956800*l_1*p_85417555>"),
MM("M<y_591h*x_604h*d_0c43h*p_115125231*l_2*p_2830080*l_2*p_33020690*l_2*t_1*l_2*p_1985280*l_1*p_53377298*t_1*l_2*p_2344320*l_2*p_47255*t_1*l_2*p_1985280*l_1*p_11156323*t_2*l_1*p_1499520*l_1*p_85335750*t_2*l_2*p_2956800*l_1*p_43151427*t_2*l_2*p_2597760*l_1*p_42796344>"),
MM("M<y_89h*x_16d6h*d_65h*p_193543987*l_2*p_1457280*l_1*p_32018212*l_2*t_2*l_1*p_2027520*l_1*p_12553324*l_2*t_2*l_1*p_1499520*l_1*p_12609254*l_1*t_2*l_2*p_1943040*l_2*p_31997026*t_1*l_1*p_2999040*l_1*p_17286*t_2*l_2*p_1943040*l_2*p_43261092*t_2*l_1*p_1499520*l_2*p_42669331>"),
MM("M<y_0d3h*x_1f20h*d_0a39h*p_174937224*l_2*p_2597760*l_1*p_22819815*t_1*l_2*p_1394880*l_2*p_2256*l_2*t_2*l_2*p_2880*l_1*p_466848*l_1*p_2556480*t_1*l_2*p_2880000*l_2*t_1*l_1*p_3840*l_2*p_929664*t_2*l_2*p_2830080*l_2*p_53436206*t_2*l_1*p_960*l_2*p_53350464*t_1*l_2*p_1985280*l_1*p_85329993>"),
MM("M<y_2bh*x_1871h*d_103h*p_161040381*l_1*p_81206400*l_1*p_189425328*l_2*t_2*l_2*p_2597760*l_1*p_1930996*l_1*t_2*l_2*p_1900800*l_2*p_33013187*l_2*t_1*l_1*p_1499520*l_1*p_53441864*t_1*l_2*p_1985280*l_1*p_85812097*t_2*l_2*p_1943040*l_2*p_96478664*t_1*l_2*p_2956800*l_1*p_42715556>"),
MM("M<y_95h*x_0db8h*d_867h*p_186045257*l_2*p_2830080*l_2*p_22795745*t_1*l_2*p_2344320*l_2*p_10882167*t_2*l_2*p_1394880*l_1*p_53436192*t_1*l_1*p_1499520*l_2*p_22748486*t_2*l_2*p_2344320*l_2*p_1421002*l_2*t_2*l_1*p_1499520*l_1*p_64017956*t_2*l_2*p_2956800*l_1*p_42795385>"),
MM("M<y_6e8h*x_0c5ah*d_0dah*p_73201788*l_1*p_46168320*l_1*t_1*l_2*p_1985280*l_1*p_11322823*t_2*l_2*p_1457280*l_1*p_152099*t_2*l_2*p_2597760*l_1*p_106661296*t_2*l_2*p_2386560*l_2*p_42710748*t_2*l_2*p_2597760*l_1*p_21419893*t_2*l_2*p_1985280*l_1*p_64083395>")]

   
y_normaliser_gens =[MM("M<y_5ddh*x_0cb8h*d_780h*p_101185443*l_1*p_1499520*l_1*p_6864*t_1*l_2*p_2956800*l_1*p_21865340*l_1*t_1*l_2*p_1858560*l_1*p_2112*l_2*p_975360*t_1*l_1*p_2417280*t_1*l_2*p_2830080*l_2*p_43634325*t_2*l_1*p_1499520*l_1*p_42734752*t_2*l_2*p_1985280*l_1*p_42677955>"),
MM("M<y_0ch*x_17dh*d_0a73h*p_192340543*l_2*p_2597760*l_1*p_43686374*t_2*l_2*p_2344320*l_2*p_467749*l_2*t_2*l_1*p_2640000*l_1*p_13037268*l_1*t_2*l_2*p_2344320*l_2*p_13458*t_2*l_2*p_2830080*l_2*p_64046787*t_2*l_1*p_1499520*l_2*p_63994958*t_1*l_2*p_1900800*l_2*p_139586*t_1*l_2*p_2386560*l_2*p_42727145>"),
MM("M<y_4fh*x_1331h*d_0d46h*p_79853974*l_2*p_1943040*l_2*p_2398522*t_1*l_2*p_2344320*l_2*p_1858757*l_2*t_1*l_1*p_960*l_2*p_3120*l_2*p_517440*t_2*l_2*p_2597760*l_1*p_12132032*t_2*l_2*p_2880*l_1*p_465840*l_1*p_1565760*t_1*l_2*p_960*l_1*p_63994992*t_1*l_1*p_2027520*l_1*p_50146>"),
MM("M<y_8dh*x_12aah*d_0e02h*p_64563918*l_2*p_2830080*l_2*p_32088530*t_2*l_2*p_2344320*l_2*p_12149352*l_1*t_2*l_1*p_1415040*l_1*p_10667856*l_2*p_4796160*t_2*l_1*p_1499520*l_2*p_53357163*t_1*l_2*p_960*l_2*p_464928*l_2*p_549120*t_1*l_1*p_1105920*l_2*t_2*l_2*p_1943040*l_2*p_85812172>")]

yt_1_normaliser_gens = [MM("M<y_6bah*x_40fh*d_8f6h*p_71067893*l_1*p_1499520*l_2*p_33443096*l_1*t_2*l_1*p_2027520*l_1*p_2859317*t_1*l_2*p_2597760*l_1*p_43159057*t_2*l_2*p_2597760*l_1*p_170651330*t_1*l_2*p_2830080*l_2*p_11602755*l_1*t_1*l_2*p_2386560*l_2*p_85371397*t_1*l_1*p_1499520*l_1*p_42756875>"),
MM("M<y_4c5h*x_194ah*d_5cfh*p_91427851*l_2*p_49272960*l_2*p_212488368*t_2*l_1*p_2640000*l_1*p_11598883*l_1*t_2*l_1*p_1457280*l_2*p_32476051*l_2*t_2*l_1*p_2027520*l_1*p_521506*t_1*l_2*p_2956800*l_1*p_106663200*t_1*l_2*p_2597760*l_1*p_42729988*t_1*l_1*p_1651200>"),
MM("M<y_92h*x_0dc5h*d_73fh*p_149085778*l_2*p_79875840*l_2*p_87859296*t_1*l_2*p_49716480*l_1*p_160152960*t_2*l_2*p_2386560*l_2*p_53795926*t_2*l_1*p_1499520*l_2*p_127992597*t_1*l_1*p_2640000*l_1*p_85370418*l_1*p_11658240*t_1*l_2*p_1394880*l_1*p_465840*l_2*p_3784320>"),
MM("M<y_503h*x_9eah*d_374h*p_233989239*l_2*p_2386560*l_2*p_23198721*l_2*t_1*l_2*p_1900800*l_2*p_22760055*l_1*t_1*l_2*p_1858560*l_1*p_10668720*l_1*p_1506240*t_1*l_1*p_2640000*l_1*p_570627*t_2*l_2*p_58143360*l_2*p_168579888*l_1*t_2>"),
MM("M<y_0e5h*x_1f3ah*d_6c9h*p_90562686*l_2*p_1943040*l_2*p_22779366*l_1*t_1*l_2*p_1457280*l_1*p_10708*l_2*t_1*l_2*p_1457280*l_1*p_21801795*l_1*t_1*l_2*p_169920*l_1*t_1*l_1*p_1499520*l_2*p_86283409*t_2*l_2*p_1985280*l_1*p_85840899*t_2*l_2*p_1457280*l_1*p_533034*t_1*l_2*p_2830080*l_2*p_42667401>"),
MM("M<y_4d7h*x_0a6eh*d_0c5ah*p_80509897*l_2*p_2386560*l_2*p_31998076*l_1*t_2*l_1*p_1499520*l_1*p_21817250*l_1*t_1*l_2*p_1985280*l_1*p_32954433*l_2*t_2*l_2*p_1457280*l_1*p_4822*t_2*l_2*p_1457280*l_1*p_2885*t_2*l_2*p_2830080*l_2*p_10702299*l_2*t_2*l_2*p_78101760*l_2*p_168136464>"),
MM("M<y_5c2h*x_0f48h*d_43bh*p_184125088*l_2*p_2344320*l_2*p_32552120*l_1*t_2*l_2*p_2386560*l_2*p_32961161*t_2*l_1*p_467520*l_1*p_951552*t_2*l_2*p_1900800*l_2*p_151143*t_1*l_2*p_1457280*l_1*p_32466467*l_1*t_1*l_2*p_2956800*l_1*p_106660342*t_2*l_2*p_2597760*l_1*p_42717490>"),
MM("M<y_136h*x_1a2dh*d_0f15h*p_106908922*l_2*p_1985280*l_1*p_53353282*t_1*l_2*p_2787840*l_2*p_32511715*l_2*t_1*l_1*p_23040*l_1*p_2370816*t_1*l_2*p_2787840*l_2*p_86282450*l_2*p_528000*t_2*l_2*p_59917440*l_1*p_152169888>"),
MM("M<y_158h*x_26fh*d_0f44h*p_175760587*l_2*p_2344320*l_2*p_32070138*l_1*t_2*l_2*p_24000*l_2*p_10665840*l_2*t_2*l_1*p_1920*l_2*p_24336*l_2*p_2556480*t_2*l_2*p_2899200*l_2*t_1*l_2*p_2386560*l_2*p_42676067*t_2*l_1*p_1457280*l_2*p_96478695*l_1*p_2880*t_1*l_2*p_58143360*l_2*p_241317120>"),
MM("M<y_472h*x_19cdh*d_397h*p_96244732*l_2*p_2830080*l_2*p_2418726*l_2*t_1*l_2*p_2956800*l_1*p_23232*l_1*t_1*l_2*p_1900800*l_2*p_2789126*l_1*t_2*l_1*p_131520*l_2*t_2*l_2*p_2956800*l_1*p_11266023*t_2*l_2*p_1943040*l_2*p_42673189*t_1*l_2*p_2956800*l_1*p_42831938*t_2*l_2*p_2830080*l_2*p_43180260>")]
   
   
yt_2_normaliser_gens = [MM("M<y_5e5h*x_1a8h*d_88h*p_158548295*l_2*p_2597760*l_1*p_42705293*t_2*l_2*p_2386560*l_2*p_12107843*l_2*t_2*l_1*p_1415040*l_1*p_10668768*l_1*p_514560*t_2*l_1*p_3338880*l_2*t_1*l_1*p_2640000*l_1*p_34689*l_1*t_1*l_1*p_2027520*l_1*p_1936*t_2*l_1*p_1499520*l_2*p_42708851>"),
MM("M<y_534h*x_1d6bh*d_0c5ch*p_5343566*l_2*p_2386560*l_2*p_33401737*l_2*t_1*l_1*p_1457280*l_2*p_10666763*l_2*t_2*l_2*p_1858560*l_2*p_23376*l_1*p_4205760*t_1*l_1*p_2640000*l_1*p_217442*t_1*l_2*p_2830080*l_2*p_22755377*l_2*t_2*l_2*p_1900800*l_2*p_3857*t_2*l_2*p_1943040*l_2*p_64025696>"),
MM("M<y_536h*x_388h*d_28fh*p_121968387*l_2*p_1457280*l_1*p_22367548*l_2*t_1*l_2*p_3840*l_1*p_464832*l_1*p_1964160*t_1*l_2*p_1943040*l_2*p_21866291*l_1*t_1*l_1*p_2027520*l_1*p_475284*t_1*l_2*p_2386560*l_2*p_64015158*t_1*l_2*p_2386560*l_2*p_42730938*t_1*l_1*p_2999040*l_1*p_176106>"),
MM("M<y_587h*x_9c4h*d_16fh*p_123045651*l_2*p_2956800*l_1*p_32018112*l_2*t_2*l_2*p_2344320*l_2*p_21865408*l_1*t_1*l_1*p_960*l_2*p_22272*l_2*p_998400*t_1*l_2*p_2597760*l_1*p_96477776*t_1*l_2*p_2386560*l_2*p_53382136*t_2*l_1*p_1499520*l_1*p_21383234*t_1*l_2*p_762240>"),
MM("M<y_549h*x_22fh*d_30dh*p_219373891*l_2*p_1457280*l_1*p_21888592*l_1*t_1*l_2*p_1985280*l_1*p_1489449*l_1*t_1*l_1*p_2999040*l_1*p_1395206*l_2*t_1*l_1*p_2027520*l_1*p_152980*t_2*l_2*p_2597760*l_1*p_53824704*t_2*l_2*p_2386560*l_2*p_53794965*t_1*l_1*p_2999040*l_1*p_5796>"),
MM("M<y_561h*x_1ac0h*d_2e1h*p_184737550*l_2*p_2787840*l_2*p_32971681*l_2*t_2*l_2*p_1943040*l_2*p_10805169*t_2*l_2*p_2830080*l_2*p_21345811*t_2*l_1*p_1499520*l_2*p_951568*t_2*l_2*p_2830080*l_2*p_53436236*t_2*l_1*p_4190400*l_1*t_1*l_2*p_2033280*l_1>"),
MM("M<y_53dh*x_1e0bh*d_0fcdh*p_243978502*l_1*p_2640000*l_1*p_21871266*l_1*t_2*l_1*p_1499520*l_1*p_12996051*t_2*l_2*p_1900800*l_2*p_6742*t_2*l_2*p_1900800*l_2*p_1016355*t_2*l_1*p_1858560*l_2*p_466800*l_1*p_4312320*t_2*l_1*p_1499520*l_2*p_64002663*t_1*l_1*p_1499520*l_1*p_64016089>"),
MM("M<y_4bch*x_196ah*d_0e32h*p_11572968*l_1*p_1499520*l_2*p_21796210*l_1*t_2*l_2*p_2830080*l_2*p_33414272*t_1*l_2*p_1985280*l_1*p_11158316*t_1*l_1*p_1499520*l_1*p_53801654*t_2*l_2*p_2597760*l_1*p_42711672*t_2*l_2*p_2597760*l_1*p_43634329*t_2*l_1*p_1499520*l_2*p_106663237>"),
MM("M<y_1e0h*x_1593h*d_5c4h*p_198886190*l_2*p_2830080*l_2*p_21817304*t_2*l_2*p_2344320*l_2*p_1523012*t_2*l_1*p_2999040*l_1*p_47170*t_1*l_1*p_951360*t_2*l_2*p_2597760*l_1*p_42754026*t_2*l_2*p_2386560*l_2*p_42835787*t_2*l_2*p_1943040*l_2*p_43594872>"),
MM("M<y_19bh*x_153ch*d_0d43h*p_118504558*l_2*p_2344320*l_2*p_33420998*l_1*t_2*l_1*p_1457280*l_2*p_33397762*l_2*t_2*l_1*p_3840*l_1*p_1296*l_1*p_10394880*t_2*l_1*p_1499520*l_2*p_22326208*t_2*l_2*p_2344320*l_2*p_1912610*l_1*t_1*l_2*p_1943040*l_2*p_43160087*t_2*l_2*p_2597760*l_1*p_85833248>")]
   
yt_3_normaliser_gens = [MM("M<y_6fh*x_1cedh*d_484h*p_125326484*l_1*p_1457280*l_2*p_2794915*l_1*t_1*l_1*p_1393920*l_2*p_3168*l_1*p_1944000*t_1*l_2*p_1457280*l_1*p_22356999*l_2*t_2*l_2*p_2597760*l_1*p_53443799*t_2*l_1*p_3840*l_2*p_22272*l_2*p_1484160*t_1*l_1*p_16874880*l_2*t_2*l_2*p_1943040*l_2*p_43198480>"),
MM("M<y_4abh*x_0cebh*d_709h*p_6736343*l_2*p_1900800*l_2*p_962066*t_1*l_1*p_2640000*l_1*p_2791184*l_1*t_1*l_1*p_1920*l_2*p_10665792*l_2*p_805440*t_1*l_2*p_2597760*l_1*p_21348683*t_2*l_1*p_1499520*l_1*p_53377339*t_2*l_2*p_2386560*l_2*p_96040852*t_1*l_2*p_2787840*l_2*p_18272>"),
MM("M<y_431h*x_9efh*d_0c8fh*p_212298532*l_1*p_2027520*l_1*p_2793088*l_2*t_2*l_2*p_1985280*l_1*p_12059808*l_1*t_2*l_1*p_2027520*l_1*p_32555960*l_1*t_2*l_1*p_2999040*l_1*p_11523*t_2*l_2*p_49716480*l_2*p_233333856*t_1*l_2*p_1415040*l_2*p_2256*l_1*p_298560*t_1*l_2*p_1943040*l_2*p_42726212*t_1*l_2*p_2597760*l_1*p_42708905>"),
MM("M<y_273h*x_1c47h*d_0a7ah*p_124228372*l_2*p_24000*l_2*p_149232*t_2*l_2*p_2830080*l_2*p_13002563*t_2*l_2*p_1900800*l_2*p_1016258*t_1*l_2*p_2830080*l_2*p_21331778*t_2*l_1*p_1499520*l_2*p_85332897*t_2*l_2*p_2956800*l_1*p_43261057*t_1*l_1*p_1566720>"),
MM("M<y_3b1h*x_106h*d_0b7dh*p_31257692*l_1*p_1457280*l_2*p_12578473*t_2*l_2*p_1985280*l_1*p_12069346*l_2*t_2*l_1*p_1499520*l_2*p_32000790*l_1*t_2*l_2*p_2597760*l_1*p_106698932*t_1*l_1*p_2640000*l_1*p_22370393*l_2*t_1*l_2*p_2787840*l_2*p_5771*t_1*l_1*p_1499520*l_2*p_85327136>"),
MM("M<y_0ebh*x_1339h*d_466h*p_184229543*l_2*p_2830080*l_2*p_23202562*l_1*t_2*l_2*p_2386560*l_2*p_22306055*l_1*t_2*l_2*p_1393920*l_2*p_1200*l_1*p_960000*t_2*l_2*p_1985280*l_1*p_64026658*t_2*l_2*p_1858560*l_2*p_22320*l_1*p_5239680*t_2*l_1*p_1499520*l_2*p_106662250*t_1*l_1*p_1499520*l_1*p_85336736>"),
MM("M<y_8ch*x_1fe0h*d_0d92h*p_225498305*l_2*p_2386560*l_2*p_21931685*t_2*l_2*p_2787840*l_2*p_8738*l_1*t_2*l_2*p_2787840*l_2*p_32064452*l_1*t_1*l_2*p_4012800*l_1*t_1*l_2*p_1943040*l_2*p_42834857*t_2*l_2*p_2597760*l_1*p_21429419*t_2*l_1*p_2640000*l_1*p_63777*t_2*l_1*p_2027520*l_1*p_4816>"),
MM("M<y_5ech*x_104h*d_0d43h*p_238213356*l_1*p_59473920*l_2*p_203174400*t_2*l_1*p_80762880*l_2*p_183216000*l_1*t_1*l_2*p_70118400*l_2*p_220915200*l_1*t_1*l_2*p_2344320*l_2*p_5777*t_2*l_2*p_2956800*l_1*p_127989713*t_1*l_1*p_1457280*l_2*p_42755906*l_1*p_22080*t_1*l_1*p_79875840*l_1*p_2682240*l_2>"),
MM("M<y_121h*x_0b4ch*d_0f29h*p_208496975*l_2*p_1900800*l_2*p_1971435*l_1*t_1*l_1*p_2027520*l_1*p_12153188*l_1*t_2*l_2*p_2787840*l_2*p_21906706*l_1*t_1*l_1*p_1499520*l_1*p_21358224*t_2*l_1*p_1499520*l_1*p_106700754*t_2*l_2*p_2956800*l_1*p_21364050*t_2*l_1*p_4671360*l_1>"),
MM("M<y_56h*x_187dh*d_760h*p_214410543*l_2*p_2956800*l_1*p_32473189*l_1*t_2*l_1*p_2999040*l_1*p_32065424*l_1*t_1*l_2*p_2956800*l_1*p_23216165*l_1*t_2*l_2*p_2597760*l_1*p_11242963*t_1*l_2*p_1985280*l_1*p_106664193*t_1*l_2*p_1943040*l_2*p_11308374*t_2*l_1*p_1499520*l_1*p_42713669>")]

###Check to see if normalisers do indeed normalise
def normaliser_check(elt,norm_gens):
   return all([elt**x in [elt**i for i in range(elt.order())] for x in norm_gens])
   
####################################################################################
### 
### Proof of Corollary 3.4
### Here we provide generators for PSL_3(3) centralising g13
### We also give a function that checks which elements in this PSL(3,3) centralise a [g13,g6,g2] tuple
###
   
L33_gens = [MM("M<y_0fh*x_0bc4h*d_59h*p_207376512*l_2*p_1943040*l_2*p_22272232*l_2*t_1*l_1*p_1499520*l_1*p_22439*l_1*t_1*l_1*p_1394880*l_1*p_21456*l_2*p_4776960*t_2*l_1*p_1499520*l_2*p_53357227*t_1*l_2*p_960*l_2*p_10665792*l_1*p_6086400*t_1*l_2*p_1943040*l_2*p_64043939*t_2*l_2*p_2956800*l_1*p_64017049>"),
MM("M<y_5a8h*x_0bcdh*d_941h*p_205645390*l_2*p_2830080*l_2*p_8690*l_2*t_1*l_2*p_1900800*l_2*p_10675420*t_1*l_2*p_2597760*l_1*p_42728016*t_2*l_2*p_2597760*l_1*p_10729207*t_1*l_2*p_1985280*l_1*p_21338086*t_2*l_2*p_2597760*l_1*p_21359269*t_1*l_1*p_1499520*l_1*p_42755907>")]

def PSL_2_13_centraliser(h13,h6,h2):
   #check orders of elements
   if h13.order() != 13 or h6.order() != 6 or h2.order() !=2:
       raise Exception("Error: elements not of right order")
   #Compute all elements in the group generated by L33_gens
   L= L33_gens
   orb  = [L[0]]
   orbset = {tuple(L[0].as_tuples())}
   os = 0
   for el in L:
       eltup = tuple(el.as_tuples())
       if not eltup in orbset:
           orb.append(el)
           orbset.add(eltup)
           os = os+1;
            
   j  = 0
   while j <= os-1:
       for g in L:
           el= orb[j]*g
           eltup = tuple(el.as_tuples())
           if not eltup in orbset:
               orb.append(el)
               orbset.add(eltup)
               os = os+1;
                   
       j = j+1
   #print("PSL3(3) has order ", len(orb))
   #Check which elements of orb centralise the L2(13) generators
   cent = []
   for k in orb:
       if h13**k==h13 and h6**k==h6 and h2**k==h2:
           cent.append(k)
   return cent
   
   
#Check the centraliser of our PSL_2(13)   
def verify_PSL_2_13_centraliser(h13,h6,h2):
   c1=all([h13**x==h13 for x in L33_gens])
   c2 = PSL_2_13_centraliser(h13,h6,h2)
   return c1 and len(c2)==1

## verify_PSL_2_13_centraliser(g13,g6,i2) returns true
