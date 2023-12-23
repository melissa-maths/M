#!/usr/bin/env python
# coding: utf-8

# # Generators for (certain) maximal subgroups of the Monster
# 
# Authors: Heiko Dietrich, Melissa Lee, and Tomasz Popiel
# 
# Date: 12 December 2023
# 
# In our paper <a href="https://arxiv.org/abs/2304.14646">The maximal subgroups of the Monster</a>, we note that we have constructed (generators for) certain maximal subgroups of the Monster $\mathbf{M}$ that were not needed for our proofs, but that might be of independent interest. 
# 
# Here we provide those generators (in <a href="https://github.com/Martin-Seysen/mmgroup">mmgroup</a> format), with proofs that they generate the claimed maximal subgroups of $\mathbf{M}$.
# 
# Where possible, we seek to construct "standard generators" as defined by <a href="https://doi.org/10.1006/jabr.1996.0271">Wilson</a> and/or the <a href="http://atlas.math.rwth-aachen.de/Atlas/v3/index.html">online Atlas</a> (of Finite Group Representations).
# 
# In some cases, we also provide additional data, e.g. conjugacy class fusion from the maximal subgroup to the Monster.
# 
# **Warning: some variable names are repeated for conciseness, so this file should be read section-by-section.**

# ## Preliminary code
# 
# Import required package(s) and define basic function(s).

# In[1]:


from mmgroup import *


# In[2]:


# Group commutator
def Comm(a,b):
   return a**(-1)*b**(-1)*a*b


# ## Generators for $2.\mathbf{B} < \mathbf{M}$
# 
# The maximal subgroup $2.\mathbf{B}$ of $\mathbf{M}$ is the centraliser of an involution of class $2\text{A}$. Our copy of this subgroup is the centraliser of the 'standard' $2\text{A}$-involution in mmgroup, namely the following element.

# In[3]:


y = MM("M<d_200h>")


# Confirm that $y$ is the standard $2\text{A}$-involution.

# In[4]:


y.conjugate_involution()


# The following elements $a$ and $b$ of $\mathbf{M}$ centralise $y$.

# In[5]:


a = MM("M<y_0bdh*x_133h*d_0b03h*p_122433352*l_1*p_71005440*l_2*p_220471680*l_2*t_2*l_2*p_60360960*l_1*p_232890288*l_2*t_1*l_2*p_59473920*l_2*p_241760688*l_1*t_1*l_1*p_13326720*l_2>")
b = MM("M<y_480h*x_15a9h*d_800h*p_55059691*l_1*p_71005440*l_1*p_199182768*t_1*l_1*p_59917440*l_1*p_242647728*l_1*t_1*l_1*p_49716480*l_1*p_240430080*l_1*t_1*l_2*p_15987840*l_2*t_1*l_2*p_141081600>")
Comm(y,a) == Comm(y,b) == MM("M<1>")


# We claim that $a$ and $b$ are "standard generators" for $C_\mathbf{M}(y) \cong 2.\mathbf{B}$. This means that $a$ and $b$ generate $C_\mathbf{M}(y)$ and satisfy the following properties:
# 
# 1. $a$ projects to the $\mathbf{B}$-class $2\text{C}$,
# 2. $b$ projects to the $\mathbf{B}$-class $3\text{A}$, 
# 3. $ab$ projects to the $\mathbf{B}$-class $55\text{A}$, 
# 4. $(ab)^3(ab^2)(ab)(ab^2)^2$ projects to an element of order $23$.
# 
# We first show that $a$ and $b$ generate $C_\mathbf{M}(y)$. It suffices to exhibit an element of order $17$ and an element of order $31$ in $\langle a,b \rangle$, because no maximal subgroup of the quotient $\mathbf{B}$ of $2.\mathbf{B}$ contains elements of both orders.

# In[6]:


((a*b*a*b*a*b*a*b**2*a*b*a*b**2*a*b*a*b)**2).order(), (a*b*a*b*a*b*a*b**2*a*b*a*b**2).order()


# It now remains to show that $a$ and $b$ satisfy conditions 1-4. 
# 
# Consider the following elements of $\mathbf{M}$, which have order $104$ and $78$, respectively, and centralise $y$.

# In[7]:


g104 = MM("M<y_9dh*x_10cbh*d_0ab9h*p_185877467*l_2*p_50603520*l_1*p_210270720*l_1*t_2*l_2*p_70561920*l_2*p_181885440*l_2*t_1*l_2*p_69231360*l_2*p_168579888*l_1*t_2*l_1*p_4012800*l_1*t_1*l_2*p_119792640>")
g78 = MM("M<y_163h*x_1489h*d_0a93h*p_107838533*l_2*p_70118400*l_2*p_12439680*t_1*l_1*p_45281280*l_2*p_71871360*l_1*t_2*l_1*p_71005440*l_2*p_179667888*l_1*t_2*l_2*p_60804480*l_1*p_152169888>")
g104.order() == 104 and g78.order() == 78 and Comm(y,g104) == Comm(y,g78) == MM("M<1>")


# Now observe that $g_{104}^{26}=a$ and $g_{78}^{13}=b$. In particular, $|a|=4$ and $|b|=6$.

# In[8]:


g104**26 == a and g78**13 == b and a.order() == 4 and b.order() == 6


# The GAP character table library indicates that 
# - all elements of order $104$ in $2.\mathbf{B}$ power to $2.\mathbf{B}$-class $4\text{A}$, and that the latter elements project to $\mathbf{B}$-class $2\text{C}$; 
# - all elements of order $78$ in $2.\mathbf{B}$ power to $2.\mathbf{B}$-class $6\text{A}$, and that the latter elements project to $\mathbf{B}$-class $3\text{A}$.
# 
# Therefore, $a$ and $b$ lie in the $2.\mathbf{B}$-classes $4\text{A}$ and $6\text{A}$ and project to the $\mathbf{B}$-classes $2\text{C}$ and $3\text{A}$, respectively. 
# 
# In particular, conditions 1 and 2 hold.
# 
# All elements of order $55$ in $2.\mathbf{B}$ project to the $\mathbf{B}$-class $55\text{A}$, so to check condition 3 it suffices to confirm that $ab$ has order $55$.

# In[9]:


(a*b).order() == 55


# Finally, to check condition 4, it suffices to confirm that the 23rd power of $(ab)^3(ab^2)(ab)(ab^2)^2$ lies in $\langle y \rangle = \{y,y^2\}$.

# In[10]:


((a*b)**3*(a*b**2)*(a*b)*(a*b**2)**2)**23 in [y, y**2]


# ## Generators for $\text{S}_3 \times \text{Th} < \mathbf{M}$
# 
# The maximal subgroup $\text{S}_3 \times \text{Th}$ of $\mathbf{M}$ is the normaliser of an element of class $3\text{C}$. Our copy of this subgroup is generated by the following four elements; the element $c_3$ is the $3\text{C}$-element being normalised. 

# In[11]:


c2 = MM("M<d_200h>")
c3 = MM("M<y_4cdh*x_1274h*d_499h*p_8151915*l_2*p_1900800*l_2*p_43255347*t_2*l_2*p_2597760*l_1*p_479249*l_2*t_2*l_1*p_4654080*t_1*l_2*p_2956800*l_1*p_53436116*t_2*l_2*p_2386560*l_2*p_85412773*t_1*l_1*p_1499520*l_1*p_106661296>")
a = MM("M<y_4ch*x_47ah*d_0e20h*p_218274859*l_1*p_49272960*l_1*p_151726128*t_1*l_1*p_74997120*l_2*p_71871360*l_1*t_2*l_1*p_60804480*l_2*p_229785600*l_1*t_1*l_1*p_58143360*l_1*p_160153296>")
b = MM("M<y_0b5h*x_955h*d_0e1h*p_197852501*l_1*p_70561920*l_1*p_232890288*l_1*t_1*l_1*p_79875840*l_1*p_203617920*l_2*t_2*l_2*p_68344320*l_2*p_202730880*l_1*t_1*l_1*p_117575040*l_1*t_2*l_1*p_109148160*l_2>")


# To prove this, first note that the elements $c_2$ and $c_3$ are the same as in the "type T" case in Listing 8 of our paper. 
# They satisfy $|c_2|=2$, $|c_3|=3$, and $c_3^{c_2} = c_3^{-1}$, so they generate a group isomorphic to $\text{S}_3$.

# In[12]:


c2.order() == 2 and c3.order() == 3 and c3**c2 == c3**-1


# The group $\langle c_2,c_3 \rangle \cong \text{S}_3$ commutes with $\langle a,b \rangle$.

# In[13]:


Comm(c2,a) == Comm(c2,b) == Comm(c3,a) == Comm(c3,b) == MM("M<1>")


# The element $a$ is of class $2B$, so we conjugate $c_3$ into mmgroup's copy of the $2\text{B}$-centraliser $2^{1+24}.\text{Co}_1$ and confirm that $c_3 \in 3\text{C}$. 
# The character of the $196883$-dimensional complex representation of $\mathbf{M}$, which is computed in mmgroup via the method chi_G_x0( )[0], should evaluate on $c_3$ to $-1$.

# In[14]:


ci_a = a.conjugate_involution()
ci_a[0] == 2 and (c3**ci_a[1]).in_G_x0() and (c3**ci_a[1]).chi_G_x0()[0] == -1


# At this point, we have established that $\langle c_2,c_3,a,b \rangle$ normalises $c_3 \in 3\text{C}$ and that $\langle c_2,c_3 \rangle$ is the direct factor $\text{S}_3$ of $N_\mathbf{M}(\langle c_3 \rangle) \cong \text{S}_3 \times \text{Th}$. 
# 
# In particular, $\langle a,b \rangle$ is a subgroup of the direct factor $\text{Th}$ of $N_\mathbf{M}(\langle c_3 \rangle)$. 
# 
# We claim that $a$ and $b$ are standard generators for $\text{Th}$. 
# This means that $\langle a,b \rangle \cong \text{Th}$ and
# 
# 1. $a$ has order $2$, 
# 2. $b$ lies in the $\text{Th}$-class $3\text{A}$, 
# 3. $ab$ has order $19$.
# 
# Conditions 1 and 3 are readily checked.

# In[15]:


a.order(), (a*b).order()


# To check condition 2, note that every element of order $39$ in $\text{Th}$ powers to $\text{Th}$-class $3\text{A}$. The following element centralises $\langle c_2,c_3 \rangle$, has order $39$, and powers to $b$. Therefore, condition 2 holds.

# In[16]:


g39 = MM("M<y_0f7h*x_4d8h*d_711h*p_106931325*l_2*p_70118400*l_1*p_190312368*l_1*t_1*l_2*p_80319360*l_1*p_222245808*l_2*t_1*l_1*p_67900800*l_1*p_11552640*l_2*t_1*l_2*p_70118400*l_1*p_179668128>")
Comm(g39,c2) == Comm(g39,c2) == MM("M<1>") and g39.order() == 39 and g39**13 == b


# It remains to show that $a$ and $b$ generate $\text{Th}$. It suffices to exhibit an element of order $31$ in $\langle a,b \rangle$, because no maximal subgroup of $\text{Th}$ contains an element of order $31$ and an element of order $19$.

# In[17]:


(a*b*a*b**2*a*b**2*a*b*a*b**2*a*b*a*b*a*b*a*b**2*a*b**2*a*b*a*b).order()


# ## Generators for $3.\text{Fi}_{24} < \mathbf{M}$
# 
# The maximal subgroup $3.\text{Fi}_{24}$ of $\mathbf{M}$ is the normaliser of an element of class $3\text{A}$. Our copy of this subgroup is the normaliser of the following element. 

# In[18]:


g3 = MM("M<y_3dbh*x_14c9h*d_1c6h*p_238425007*l_2*p_1985280*l_1*p_11174636*l_2>")


# This element has order $3$ and lies in mmgroup's copy of the $2\text{B}$-centraliser $2^{1+24}.\text{Co}_1$, so we can confirm that it is of class $3\text{A}$ by checking that its character value in the $196883$-dimensional complex representation of $\mathbf{M}$ is $782$.

# In[19]:


g3.order() == 3 and g3.in_G_x0() and g3.chi_G_x0()[0] == 782


# We claim that the following elements $a$ and $b$ are standard generators for $N_\mathbf{M}(\langle g_3 \rangle) \cong 3.\text{Fi}_{24}$. This means that $a$ and $b$ generate $N_\mathbf{M}(\langle g_3 \rangle)$ and that
# 
# 1. $a$ projects to class $2\text{C}$ in the quotient $N_\mathbf{M}(\langle g_3 \rangle) / \langle g_3 \rangle \cong \text{Fi}_{24} = \text{Fi}_{24}'{:}2$, 
# 2. $b$ projects to class $8\text{D}$ in $\text{Fi}_{24}$, and
# 3. $|ab| = 29$.

# In[20]:


a = MM("M<y_5f6h*x_0fbeh*d_2ebh*p_193227272*l_2*p_2830080*l_2*p_32067203*t_2*l_2*p_2344320*l_2*p_12596663*l_1*t_2*l_2*p_1415040*l_1*p_21817200*l_2*t_2*l_2*p_1943040*l_2*p_22351232*l_2*t_1*l_1*p_2027520*l_1*p_13443*t_2*l_1*p_1457280*l_2*p_53938>")
b = MM("M<y_743h*x_11f4h*d_391h*p_92316215*l_1*p_2999040*l_1*p_467894*t_1*l_1*p_2999040*l_1*p_26931*l_1*t_2*l_2*p_1900800*l_2*p_33465249*l_1*t_1*l_2*p_2830080*l_2*p_85326162*t_2*l_1*p_1457280*l_2*p_129106*t_2*l_1*p_1499520*l_2*p_1485571*l_1*t_1*l_2*p_2597760*l_1*p_53391808*t_2*l_1*p_1499520*l_2*p_42667429>")


# First note that $a$ and $b$ normalise $\langle g_3 \rangle$ (both invert $g_3$) but do not lie in $\langle g_3 \rangle$.

# In[21]:


g3**a == g3**b == g3**-1 and not(a in [g3,g3**2,g3**3]) and not(b in [g3,g3**2,g3**3])


# Moreover, $|a|=2$ and $|b|=8$ are coprime to $3$, so $a$ and $b$ project to elements of their respective orders in $N_\mathbf{M}(\langle g_3 \rangle) / \langle g_3 \rangle \cong \text{Fi}_{24}$.

# In[22]:


a.order(), b.order()


# The character table of $\text{Fi}_{24}$ in GAP indicates that all elements of order $46$ power to class $2\text{C}$, and that all elements of order $40$ power to class $8\text{D}$. The following elements normalise $\langle g_3 \rangle$, have order $46$ and $40$, respectively, and power to $a$ and $b$, respectively, so it follows that conditions 1 and 2 hold.

# In[23]:


g46 = MM("M<y_5feh*x_1f1h*d_292h*p_192994065*l_2*p_60360960*l_1*p_230672640*t_1*l_2*p_1985280*l_1*p_12135864*l_1*t_2*l_1*p_1457280*l_2*p_36672*l_1*t_2*l_2*p_2597760*l_1*p_63996822*t_1*l_2*p_1943040*l_2*p_11604637*l_2*t_1*l_2*p_1943040*l_2*p_63998817*t_2*l_2*p_2956800*l_1*p_42706001>")
g40 = MM("M<y_57fh*x_1d3h*d_603h*p_39537390*l_2*p_2344320*l_2*p_53820870*t_2*l_1*p_1457280*l_2*p_464944*l_2*t_1*l_2*p_1985280*l_1*p_32547596*l_2*t_2*l_2*p_1943040*l_2*p_43600722*t_1*l_2*p_1985280*l_1*p_42731872*t_2*l_2*p_1457280*l_1*p_71216*t_2*l_2*p_2956800*l_1*p_106698940>")


# In[24]:


g3**g46 == g3**g40 == g3**-1 and g46.order() == 46 and g40.order() == 40 and g46**23 == a and g40**5 == b


# Finally, condition 3 also holds.

# In[25]:


(a*b).order()


# ## Generators for $\text{PSL}_2(29){:}2 < \mathbf{M}$
# 
# The maximal subgroup $\text{PSL}_2(29){:}2$ of $\mathbf{M}$ is not explicitly discussed in our paper, but one reason for constructing a copy of it is that the conjugacy class fusion from $\text{PSL}_2(29){:}2$ to $\mathbf{M}$ had not previously been entirely determined (and was therefore not yet stored in the GAP character table library).
# 
# <a href="https://doi.org/10.1006/jabr.2001.9037">Holmes and Wilson</a> proved that $\mathbf{M}$ has a unique conjugacy class of subgroups isomorphic to $\text{PSL}_2(29)$, and that every such subgroup extends to a maximal subgroup of the form $\text{PSL}_2(29){:}2 = \text{Aut}(\text{PSL}_2(29))$. It therefore suffices to construct any $\text{PSL}_2(29){:}2 < \mathbf{M}$. 
# 
# Consider the following elements, noting that $a$ is the standard $2\text{B}$-involution in mmgroup, i.e. the center of the distinguished $2\text{B}$-centraliser $\mathbf{G} \cong 2^{1+24}.\text{Co}_1$.

# In[26]:


a = MM("M<x_1000h>")
b = MM("M<y_0a7h*x_51fh*d_0d58h*p_43929380*l_2*p_2344320*l_2*p_11172722*t_2*l_1*p_1457280*l_2*p_572681*t_1*l_2*p_2830080*l_2*p_64084352*t_1*l_2*p_1943040*l_2*p_85812140*t_1*l_2*p_2386560*l_2*p_42676049*t_1*l_2*p_2830080*l_2*p_85373280*t_1*l_2*p_2386560*l_2*p_42666435>")


# <a href="https://doi.org/10.1017/S0013091500022239">Robertson and Williams</a> show that $\text{PSL}_2(29){:}2$ has the following presentation: 
# 
# $\langle a,b \mid a^2 = b^{29} = (ab^2)^4 = (abab^2)^3 = 1 \rangle$.
# 
# Our elements $a$ and $b$ satisfy this presentation.

# In[27]:


a**2 == b**29 == (a*b**2)**4 == (a*b*a*b**2)**3 == MM("M<1>")


# It follows from Von Dyck's Theorem that $\langle a,b \rangle \cong \text{PSL}_2(29){:}2$ or $\text{PSL}_2(29)$. The latter group has no elements of order $28$, so to show that $\langle a,b \rangle \cong \text{PSL}_2(29){:}2$ it now suffices to exhibit an element of order $28$ in $\langle a,b \rangle$.

# In[28]:


(a*b).order()


# We now turn to the question of class fusion. Let $P = \langle a,b \rangle \cong \text{PSL}_2(29){:}2$. We claim that 
# * all elements of order $28$ in $P$ lie in the $\mathbf{M}$-class $28\text{D}$, and
# * all elements of order $30$ in $P$ lie in the $\mathbf{M}$-class $30\text{G}$.
# 
# The power maps in the character tables of $P$ and $\mathbf{M}$ then imply that every other non-trivial $P$-class fuses to one of the following $\mathbf{M}$-classes: 
# 
# $2\text{B}$, $3\text{B}$, $4\text{D}$, $5\text{B}$, $6\text{E}$, $7\text{B}$, $10\text{E}$, $14\text{C}$, $15\text{C}$.
# 
# The group $P$ has unique conjugacy classes of cyclic subgroups of order $28$ and $30$, and all conjugacy classes of elements of order $28$ or $30$ in $\mathbf{M}$ are rational, so to prove the claim it suffices to check a single element of each order in $P$.
# 
# Let $\chi_\mathbf{M}$ denote the character of the $198663$-dimensional complex representation of $\mathbf{M}$. 
# 
# The following element of $P$ has order $28$ and powers to a $2\text{B}$-involution, so we can conjugate it into $\mathbf{G}$ and calculate that its $\chi_\mathbf{M}$-value is $1$. This indicates that the element lies in the $\mathbf{M}$-class $28\text{D}$ as claimed.

# In[29]:


g28 = a*b
ci_g28 = (g28**14).conjugate_involution()
g28.order() == 28 and ci_g28[0] == 2 and (g28**ci_g28[1]).in_G_x0() and (g28**ci_g28[1]).chi_G_x0()[0] == 1


# The following element of $P$ has order $30$ and commutes with the standard $2\text{B}$-involution $a$, i.e. it lies in $\mathbf{G}$, so calculate directly that its $\chi_\mathbf{M}$-value is $0$. This indicates that the element lies in the $\mathbf{M}$-class $30\text{G}$ as claimed.

# In[30]:


g30 = a*b**2*Comm(a,a*b**2)**7
g30.order() == 30 and g30.in_G_x0() and g30.chi_G_x0()[0] == 0

