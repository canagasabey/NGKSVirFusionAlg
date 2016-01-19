import copy	
from time import time
import pdb	
import collections
import itertools
from sage.matrix import matrix_symbolic_dense



################################################################################
#
#				Virasoro Modes
#
#######################################################################################
			
class L(object):
	is_commutative = False
			
	def __init__(self,n, coeff=None):
		self.n = n
	   	   						  
	def __repr__(self):
		return 'L({})'.format(self.n)
		   	
	def __eq__(self,other):
		return self.n==other.n and isinstance(other,L)
			
	def __ne__(self,other):
		result = self.__eq__(other)
		if result is NotImplemented:
			return result
		return not result	



##############################################################################################
#														
# 					Superfield Modes					
#														
#################################################################################			

class G(object):
	is_commutative = False
			
	def __init__(self,n):
		self.n = n
	   						  
	def __repr__(self):
		return 'G({})'.format(self.n)
		   
	def __eq__(self,other):
		return self.n==other.n and isinstance(other, G)
	
	def __ne__(self,other):
		result = self.__eq__(other)
		if result is NotImplemented:
			return result
		return not result







############################################################################################
#
# 					Operator sorting algorithm
#
############################################################################################

class op(object):
	is_commutative = False
	global c
	def __init__(self,state, coeff=None):
		self.state = state
		if coeff is None:
			self.coeff = 1
		else:
			self.coeff = coeff
		
	def sortEngine(self,out=None):
		
		
		if out is None:
			self.out = []
		else:
			self.out = out
		
		##################################### Find index of first pair of operators to swap #################################################
		try:
			iswap = [isinstance(p,eps) or (isinstance(p and q,(L,G)) and p.n>q.n ) or (isinstance(p and q,G) and p.n==q.n) for p,q in zip(self.state[:-1],self.state[1:])].index(True)
		except:
			self.out.append(self)
			return self


		pre = self.state[:iswap]
		post = self.state[iswap+2:]
		p = self.state[iswap]
		q = self.state[iswap+1]
		if isinstance(p,eps) and isinstance(q,L):
			op(pre + [L(q.n),eps()] + post, self.coeff).sortEngine(self.out)
		elif isinstance(p,eps) and isinstance(q,G):
			op(pre + [G(q.n),eps()] + post, -self.coeff).sortEngine(self.out)
		elif isinstance(p,eps) and isinstance(q,eps):
			op(pre + post, self.coeff).sortEngine(self.out)


		if isinstance(p,(L,G)) and isinstance(q,(L,G)):
			m = p.n
			n = q.n
		if (isinstance(p,L) and isinstance(q,L)):
			op(pre + [L(n),L(m)] + post, self.coeff).sortEngine(self.out)
			op(pre+[L(m+n)]+post,(m-n)*self.coeff).sortEngine(self.out)

			if m+n==0:
				if len(pre+post)==0: 
					self.out.append(op([], c/12*(m**3-m)*self.coeff))				
				else: 
					op(pre + post, c/12*(m**3-m)*self.coeff).sortEngine(self.out)

		elif (isinstance(p,L) and isinstance(q,G)):
			op(pre + [G(n),L(m)] + post, self.coeff).sortEngine(self.out)
			op(pre+[G(m+n)]+post,(m/2-n)*self.coeff).sortEngine(self.out)

		elif (isinstance(p,G) and isinstance(q,L)):
			op(pre + [L(n),G(m)] + post, self.coeff).sortEngine(self.out)
			op(pre+[G(m+n)]+post,-(n/2-m)*self.coeff).sortEngine(self.out)
		elif (isinstance(p,G) and isinstance(q,G)):
			if m == n:
				op(pre + [L(m+n)] + post, self.coeff).sortEngine(self.out)
				if m+n==0:
					if len(pre+post)==0: 
						self.out.append(op([], c/6*(m**2-1/4)*self.coeff))				
					else: 
						op(pre + post, c/6*(m**2-1/4)*self.coeff).sortEngine(self.out)
		
			else:
				op(pre + [G(n),G(m)] + post, -self.coeff).sortEngine(self.out)
				op(pre+[L(m+n)]+post,2*self.coeff).sortEngine(self.out)

			# This is the central term
				if m+n==0:
					if len(pre+post)==0: 
						self.out.append(op([], c/3*(m**2-1/4)*self.coeff))				
					else: 
						op(pre + post, c/3*(m**2-1/4)*self.coeff).sortEngine(self.out)
		
		return self


 		
	def sort(self):
	   	
		thing = self.sortEngine()
		
		if len(thing.out)==1:
			return thing.out[0]
		else:
			return thing.out

	def __rmul__(self, other):
		return self.__mul__(other)
		  
	def __mul__(self, other):
		if type(other) in (Integer,Rational,Expression):
			return op(self.state, self.coeff*other)
		if isinstance(other, eps):
			self.state.append(eps())
			return self
		elif isinstance(other,list):
			things = []
			for o in other:
				things.append(self*o)
			return RemoveBrackets(things)
		else:
			return op(self.state + other.state, self.coeff*other.coeff).sort()
	  
	def __repr__(self):
		
		word = ''
		for letter in self.state:
			word +='{}'.format(letter)
		if self.coeff == 1:
			return word
		elif self.coeff == -1:
			return '-' + word
		else:
			return  '{}'.format(self.coeff) + word
		   
	def __eq__(self,other):
		if other is None:
			return False
		else:
			return self.state==other.state








############################################################
#
#					Graded Basis
#
###########################################################

def AddLetter(p,b ,out):

	if len(p) == 1:
		c = copy.deepcopy(b)
		b.state += [G(-p[0])]
		c.state += [L(-p[0])]
		out.append(b)
		out.append(c)
	elif p[0] == p[1]:
		b.state += [L(-p[1])]
		AddLetter(p[1:],b,out)
		return out
	elif p[0] != p[1]:
		c = copy.deepcopy(b)
		b.state += [G(-p[0])]
		AddLetter(p[1:],b,out)
		c.state += [L(-p[0])]
		AddLetter(p[1:],c,out)
		return out
	return out

def strictly_decreasing(L):
    return all(x>y for x, y in zip(L, L[1:]))

def non_increasing(L):
    return all(x>=y for x, y in zip(L, L[1:]))

def MakeBasis(grade,sector):
	
	basis = []
	
	if sector=='v':	
					
		for part in Partitions(grade).list():
					
			basis.append(op([L(-i) for i in part]))
					
	elif sector == 'ns':
			
		for part in Partitions(int(2*grade)).list():
					
			if all(x%2==0 or (x%2==1 and y==1) for x,y in collections.Counter(part).items()):
					
				basis.append(op([L(-i/2) if i%2==0 else G(-i/2) for i in part]))
					
	elif sector == 'r': 
		if grade == 0:
			return [op([])], [op([G(0)])]
		basis = []
		bos_basis = []
		ferm_basis = []		
		for part in Partitions(grade).list():
			basis.extend(AddLetter(part,op([]),[]))

		for b in basis:
			c = copy.deepcopy(b)
			c.state = c.state + [G(0)]
			# Only return even monomials
				
			if sum(isinstance(i,G) for i in b.state)%2==0:
				if b.state != [L(-1)]*grade:
					bos_basis.append(b)
					ferm_basis.append(c)
			else:
				if b.state != [L(-1)]*grade + [G(0)]:
					ferm_basis.append(b)
					bos_basis.append(c)


	
				"""
				elif i== len(part):
			
					#if non_increasing(permpart):# and strictly_decreasing(permpart[:i]): 					
					b = op([L(-j) for j in part])
					
					c = copy.deepcopy(b)
					c.state = c.state + [G(0)]
					# Only return even monomials
						
					if sum(isinstance(i,G) for i in b.state)%2==0:
						if b.state != [L(-1)]*grade:
							bos_basis.append(b)
							ferm_basis.append(c)
					else:
						if b.state != [L(-1)]*grade + [G(0)]:
							ferm_basis.append(b)
							bos_basis.append(c)
				"""

		bos_basis.append(op([L(-1)]*grade))
		ferm_basis.append(op([L(-1)]*grade+[G(0)]))
		basis = bos_basis, ferm_basis
					
	return basis	
	





###################################################################################
#
#	Kill positive modes acting on vacuum and replace L0 with conf dim
#
##################################################################################

def repr(inp,h):
	
	if type(inp)==list:
		out=[]
	
		for item in inp:
			rep = repr(item, h)
			if rep!= 'empty':
				out.append(rep)
	
		return out
	
	#if type(inp)==Integer:
	#	if inp==0:
	#		return "empty"
	#	else:
	#		return inp*op([L()])
	if inp.coeff==0:
		return 'empty'
	if len(inp.state)==0 or inp.state[-1].n<0 or inp.state[-1]==G(0):
		return inp	
	elif inp.state[-1]==L(0):      # We don't want G(0) to act as L(0)
		if h==0:
			return "empty"
		else:
			inp.state.remove(L(0))
			inp.coeff *=h
			return repr(inp, h)
	else:
		return "empty"
	
def ListTensRepr(ListInp,h1,h2):
   		
	#global lsector
			
	if type(ListInp)!= list:
		print 'NOT A LIST', ListInp
		print
		pdb.set_trace()
		
		
	out=[]	
		
	#if lsector=='ns' or lsector=='r':														
		
	#	ListInp = EpsilonTensList(ListInp, tensor(op([]), op([])))
		
	for tens in ListInp:
		if tens.coef()==0:	
			next
		else:
			l = repr(tens.left, h1)
			r = repr(tens.right, h2)
			if l!="empty" and r!="empty":
				out.append(tens.coeff*tensor(l,r))
		   
	return out






########################################################################
#	
# 				Find singular vector
#	
##########################################################################
		
def SingVec(svgrade,h,sector):
		
	global t_value
	
	#b1 = [[op([G(-1),G(0)])],[op([G(-1)])]]		
	#b2 = [[op([G(-2),G(0)]),op([L(-2)])],[op([G(-2)]),op([L(-2),G(0)])]]	
	#pdb.set_trace()
	if sector == 'r':
		out = [[],[]]
		for s in range(2):
			
			c, d = L(1), G(1)

			#basis = b2[s]
			#basis_same = b1[s]
			#basis_swap = b1[(s+1)%2]

			basis = MakeBasis(svgrade, 'r')[s]
			basis_same = MakeBasis(svgrade-1, 'r')[s]
			basis_swap = MakeBasis(svgrade-1, 'r')[(s+1)%2]
		
			coeff_mat=[[0]*len(basis) for i in range(len(basis_same+basis_swap))]
			
			
			
			for col,state in enumerate(basis):
				s1 = repr(op([c])*state,h)
				s2 = repr(op([d])*state,h)
				
				for p in s1:
					for row, bstate in enumerate(basis_same):
						if p == bstate:
							coeff_mat[row][col] += p.coeff
		
				for p in s2:
					for row, bstate in enumerate(basis_swap):
						if p == bstate:
							coeff_mat[len(basis_same) + row][col] += p.coeff
		
			
			C = matrix(coeff_mat)
			#return C
			singvec = kernel(C.transpose()).basis()[0]
	
			for index, coeff in enumerate(singvec):
				if coeff!=0:
					out[s].append(coeff*basis[index])
   		
		return out[0], out[1]
		
		
	if sector == 'v':
		a, b = 1,2
		c, d = L(a),L(b)
	elif sector == 'ns':
		a,b = 1/2, 3/2
		c,d = G(a), G(b)
	else:
		print 'no such sector!'
		return
	
	if svgrade in (1/2,1):
		basis = MakeBasis(svgrade, sector)	
		basis_1 = MakeBasis(svgrade-a, sector)	
		basis_2 = []
	else:
		basis = MakeBasis(svgrade, sector)	
		basis_1 = MakeBasis(svgrade-a, sector)	
		basis_2 = MakeBasis(svgrade-b, sector)
		
	coeff_mat=[[0]*len(basis) for i in range(len(basis_1)+len(basis_2))]
	
	for col,state in enumerate(basis):
		sort_states1 = op([c])*state
		sort_states2 = op([d])*state
		simp_states1 = repr(sort_states1,h)
		simp_states2 = repr(sort_states2,h)
	
		for index in range(len(simp_states1)):
			for row, bstate in enumerate(basis_1):
				if simp_states1[index] == bstate:
					coeff_mat[row][col] += simp_states1[index].coeff
	
		for index in range(len(simp_states2)):
			for row, bstate in enumerate(basis_2):
				if simp_states2[index]==bstate:
					coeff_mat[len(basis_1)+row][col] +=simp_states2[index].coeff
		
	########################################################################################
    # The coefficient of L(-1)^svgrade is always 1 so remove last col and move to the right
    #########################################################################################
	
	C = matrix(coeff_mat)
															
	#if type(C) == sage.matrix.matrix_symbolic_dense.Matrix_symbolic_dense:				######## NEED TO SPECIFY t here to solve matrix
	#	C = matrix(QQ,C(t=t_value))
	D = C[:,0:(len(basis)-1)]
	z = -1*C.column((len(basis)-1))
	singvec = -1*D\z
	things = []
		
	for index, coeff in enumerate(singvec):
		things.append(coeff*basis[index])
   		
	return things
		
		
	
	
	
	
	
	
#############################################################################
#
#					TENSORS PRODUCTS!
#
#############################################################################


def RemoveBrackets(listinput):
	return flatten(listinput)
	out = []
	for a in listinput:
		if isinstance(a, list):
			out.extend(a)
		else:
			out.append(a)
		   
	return out
		
def MakeList(inp):
		
	if isinstance(inp,list):
		return inp					
	else:
		return [inp]
		
def tensor(left, right, coeff=1):
	is_commutative = False
		
	if isinstance(left, list) and isinstance(right, list):
		
		tensorlist=[]
		for i in left:
			for j in right:
				tensorlist.append(tensorbase(i,j,coeff))
		return tensorlist
		
	elif isinstance(left, list):
		
		tensorlist=[]
		for item in left:
			tensorlist.append(tensorbase(item, right, coeff))
		return tensorlist
		
	elif isinstance(right, list):
		
		tensorlist=[]
		for item in right:
			tensorlist.append(tensorbase(left, item, coeff))
		return tensorlist
		
	else:
		
		return tensorbase(left, right, coeff)
	
class tensorbase(object):
	is_commutative = False
	
	def __init__(self, left, right, coeff):
		self.left = left
		self.right = right
		self.coeff = coeff

	def coef(self):
		if isinstance(self.left, op) and isinstance(self.right, op):
			return self.coeff*self.left.coeff*self.right.coeff
		elif isinstance(self.left, op):
			return self.coeff*self.left.coeff   
		elif isinstance(self.right, op):
			return self.coeff*self.right.coeff
		else:
			return self.coeff	
	   
	def __repr__(self):
		if self.coeff==1:
			return 'tens({},{})'.format(self.left, self.right)
		else:
			return '{}*tens({},{})'.format(self.coeff, self.left, self.right)
	
	def __str__(self):
		if self.coeff==1:
			return 'tens({},{})'.format(self.left, self.right)
		else:
			return '{}*tens({},{})'.format(self.coeff, self.left, self.right)
	   
	def __add__(self,other):
		if isinstance(other, list):
			return [tensor(self.left, self.right, self.coeff)] + other
		else:
			if self.left==other.left and self.right==other.right:
				return tensor(op(self.left.state), op(self.right.state),self.coef() + other.coef())
			else:
				return [tensor(self.left, self.right,self.coeff)] + [tensor(other.left, other.right,other.coeff)]
   
	def __radd__(self, other):
		return self.__add__(other)

	def __mul__(self, other):
		if type(other) in (Integer,Rational,Expression):
			return tensor(self.left,self.right, self.coeff*other)
		elif isinstance(other,list):
			things = []
			for o in other:
				things.append(self*o)
			return RemoveBrackets(things)
		else:
			return tensor(self.left*other.left, self.right*other.right,self.coeff*other.coeff)	   
	
	def __rmul__(self, other):
		
		if type(other) in (Integer,Rational,Expression):
			return tensor(self.left,self.right, self.coeff*other)
		elif isinstance(other,list):
			things = []
			for o in other:
				things.append(o*self)
			return RemoveBrackets(things)
		else:
			return tensor(other.left*self.left, other.right*self.right,self.coeff*other.coeff)

	def __eq__(self,other):
		return self.left==other.left and self.right==other.right
		   











#########################################################
#	
#			FUSION PRODUCT BASIS
#	
###########################################################
		
def FusionBasis((r1,s1), (r2,s2),depth):
		
	global lsector, rsector
	global alpha1, alpha2	
	
	
	if lsector!= 'v' and rsector!='v':	
		svlgrade = r1*s1/2
		svrgrade = r2*s2/2
		if r1%2==s1%2:
			lsec = 'ns'
		else:
			lsec = 'r'
		if r2%2 == s2%2:
			rsec = 'ns'
		else:
			rsec = 'r'
	else:
		svlgrade = r1*s1
		svrgrade = r2*s2
	
	h1 = ConfWeight((r1,s1),lsector)
	h2 = ConfWeight((r2,s2),rsector)
	
	############################################
	# Sage treats a/b*b as a Rational so fix here
	############################################
	
	if svlgrade*2%2 == 0:
		svlgrade = Integer(svlgrade)
	if svrgrade*2%2 == 0:
		svrgrade = Integer(svrgrade)
	
	
			
	out = []
		
   		
	if lsector == 'v':
		for i in range(svlgrade):
			out.append( tensor(op([L(-1)]*i), op([])) )
	
		
	elif lsec =='ns':
		for i in range(int(2*svlgrade)): 			
			if i%2==0:
				out.append( tensor(op([L(-1)]*int(i/2)), op([])) )
			else:
				out.append(tensor(op([L(-1)]*int((i-1)/2) + [G(-1/2)]), op([])))
	
		
	elif lsec =='r':
		if (r1,s1) == (1,1):
			out.append(tensor(op([]),op([])))
		else:
			out.append(tensor(op([]),op([])))
			for i in range(0,-3/2-alpha1,-1):
				out.append(tensor(op([G(i)]),op([])))
			for j in range(1,svlgrade):
				out.append(tensor(op([L(-1)]*j),op([])))
				out.append(tensor(op([L(-1)]*j+[G(0)]),op([])))

		
	real_out = []	
	
	if rsector == 'v':
		for o in out:
			for j in range(depth+1):
				basis_j = MakeBasis(j, rsector)
				for state in basis_j:
					if state.state[-svrgrade:] == [L(-1)]*svrgrade:
						next
					else:
						real_out.append(tensor(o.left,state))
		
	elif rsec =='ns':
		for o in out:
			for j in range(int(2*depth+1)):
				basis_j = MakeBasis(j/2, rsec)
				for state in basis_j:
					if state.state[-ceil(svrgrade):] == [L(-1)]*ceil(svrgrade):
						next
					elif type(svrgrade) is Integer and state.state[-svrgrade-1:] == [L(-1)]*int(svrgrade) + [G(-1/2)]:
						next
					elif svrgrade*2%2==1 and state.state[-int(svrgrade+1/2):] == [L(-1)]*(int(svrgrade-1/2)) + [G(-1/2)]:
						next		
					else:
						real_out.append(tensor(o.left, state))
			


			Gset = [G(-i/2) for i in range(1,2*(depth-alpha1)+1) if i%2==1]
			Lset = [L(-i) for i in range(1,depth+1)]
			
			
			for prodlength in range(1,depth-alpha1+1/2+1):
				
				for prod in itertools.combinations_with_replacement(Gset + Lset,prodlength):
					#prod = sorted(prod,reverse=True)
					extrastate = MakeList(op([a for a in prod]).sort())[0]
					extrastate.coeff = 1

					Lmodes = [l for l in extrastate.state if isinstance(l,L)]
					Gmodes = [g  for g in extrastate.state if isinstance(g,G)]
			

					
					#print Lmodes+Gmodes
					deg1 = sum([-l.n for l in Lmodes]) + sum([-g.n for g in Gmodes])
					deg2 = sum([-l.n for l in Lmodes]) + sum([-g.n + alpha1 for g in Gmodes])
					if  deg1 > depth and deg2 <= depth:
						
						if extrastate.state[-ceil(svrgrade):] == [L(-1)]*int(svrgrade):
							next
						elif type(svrgrade) is Integer and extrastate.state[-svrgrade-1:] == [L(-1)]*int(svrgrade) + [G(-1/2)]:
							next
						elif svrgrade*2%2==1 and extrastate.state[-int(svrgrade+1/2):] == [L(-1)]*(int(svrgrade-1/2)) + [G(-1/2)]:
							next	
						else:
							real_out.append(tensor(o.left,extrastate))
		
				
	elif rsec =='r':
		for o in out:
			for j in range(depth+1):
				basis_j = MakeBasis(j, rsec)[0]	+ 	MakeBasis(j, rsec)[1]
				for state in basis_j:
					if state.state[-ceil(svrgrade):] == [L(-1)]*int(svrgrade):
						next
					elif state.state[-ceil(svrgrade)-1:] == [L(-1)]*int(svrgrade) + [G(0)] :
						next
					elif j>depth and any([isinstance(i,L) and -i.n>depth for i in state.state]):
						next 
					else:
						real_out.append(tensor(o.left,state))

			#####################################################################################################
			#
			# Here we add monomials G(-m1)G(-m2)...G(-mk) such that depth< sum(mi) <=depth-k*alpha1 
			#	where mi \in {1,2,..,depth-alpha1}
			#
			######################################################################################################
			Gset = [G(-i) for i in range(1,depth-alpha1+1)]
			Lset = [L(-i) for i in range(1,depth+1)]

			

			for prodlength in range(1,depth-alpha1+1):
				for prod in itertools.combinations_with_replacement(Gset + Lset,prodlength):
					#prod = sorted(prod,reverse=True)
					Lmodes = [l for l in prod if isinstance(l,L)]
					Gmodes = [g  for g in prod if isinstance(g,G)]
					
					#print Lmodes+Gmodes
					deg1 = sum([-l.n for l in Lmodes]) + sum([-g.n for g in Gmodes])
					deg2 = sum([-l.n for l in Lmodes]) + sum([-g.n + alpha1 for g in Gmodes])
					if  deg1 > depth and deg2 <= depth:
						extrastate = MakeList(op([a for a in prod]).sort())[0]
						extrastate.coeff = 1
						if extrastate.state[-ceil(svrgrade):] == [L(-1)]*int(svrgrade):
							next
						else:
							real_out.append(tensor(o.left,extrastate))
							real_out.append(tensor(o.left,extrastate*op([G(0)])))

			

	return real_out
	
	
	





	
#########################################################################################
#
#                              Twisted Coproduct Formulae
#
##########################################################################################
			
def DeltaGnTildeRidout(n, side, N):
	
	global alpha1, alpha2

	# Superfield dimension
	h=3/2																			
	# Upper Limit of sum
	N = 10
	out = []
	
	a1 = alpha1
	a2 = alpha2
	a = a1 + a2
		
	z = var('z')
	
	if n>=1-h-a:		
						
						
		if side == 'left':
		# The (z1,z2) = (0,-z) coproduct or squiggly product
						
			for j in range(1,N):
				coeff = binomial(-a2,j)*z**(-a2-j)
				out.append(coeff*tensor(op([G(n+a2+j)]),op([])))
			for m in [k-h-a2 for k in range(1,N)]:
				coeff = binomial(n+h+a2-1,m+h+a2-1)*(-z)**(n-m)
				out.append(coeff*tensor(op([eps()]),op([G(m)])))
			
			# This is the final term that we want
			out.append(z**(-a2)*tensor(op([G(n+a2)]),op([])))
		
		elif side == 'right':				
			for m in [k-h-a1 for k in range(1,N)]:
				coeff = binomial(n+h+a1-1,m+h+a1-1)*z**(n-m)
				out.append(coeff*tensor(op([G(m)]),op([])))
																		
			for j in range(1,N):
				coeff = binomial(-a1,j)*(-z)**(-j-a1)
				out.append(coeff*tensor(op([eps()]),op([G(n+a1+j)])))
			
			# This is the final term that we want
			out.append((-z)**(-a1)*tensor(op([eps()]),op([G(n+a1)])))

	elif side == 'left':
		
		for j in range(1,N):
			coeff = binomial(-a2,j)*z**(-j-a2)
			out.append(coeff*tensor(op([G(n+a2+j)]),op([])))
		
		for m in [k-h-a2 for k in range(1,N)]:
			coeff = binomial(m-n-1,m+h+a2-1)*(-1)**(m+h+a2-1)*(-z)**(-m+n)
			out.append(coeff*tensor(op([eps()]), op([G(m)])))
		
		# This is the final term that we want
		out.append(z**(-a2)*tensor(op([G(n+a2)]),op([])))
		
	elif side == 'right':
		
		for m in [k-h-a1 for k in range(1,N)]:
			coeff = binomial(m-n-1,m+h+a1-1)*(-1)**(m+h+a1-1)*(z)**(-m+n)
			out.append(coeff*tensor(op([G(m)]),op([])))
		
		for j in range(1,N):
			coeff = binomial(-a1,j)*(-z)**(-j-a1)
			out.append(coeff*tensor(op([eps()]),op([G(n+a1+j)])))
			
		# This is the final term that we want
		out.append((-z)**(-a1)*tensor(op([eps()]),op([G(n+a1)])))

	return out
	
			


def DeltaLnz(n, side):
	h=2																				 # Virasoro conf dim
	M=10																			 # Upper Limit of sum
	out = []
			
	z = var('z')
	
	if n>=1-h:
		for m in range(1-h,n+1):
			out.append(binomial(n+h-1, m+h-1)*z**(n-m)*tensor(op([L(m)]),op([])))		
			
		if side=='left':
			return [tensor(op([]),op([L(n)]))] + out
		elif side=='right':
			return out + [tensor(op([]),op([L(n)]))]
			
	elif side == 'left':
		for m in range(1-h,M):
			out.append(binomial(m-n-1, -n-h)*(-1)**(n+h-1)*z**(n-m)*tensor(op([]), op([L(m)])))
		out.append(tensor(op([L(n)]),op([])))
			
	elif side == 'right':
		for m in range(1-h,M):
			out.append(binomial(m-n-1, -n-h)*(-1)**(m+h-1)*z**(n-m)*tensor(op([L(m)]),op([])))
		out.append(tensor(op([]),op([L(n)])))
   			
	return out



def Delta(o, side, depth):
	
	
	#######################################################
	# Here Delta(o..) returns the coproduct formula that contains o
	# Taking into account the twist parameters. For example, in the (NS,R) case
	# G(-3/2) x 1 is found in the G(-2) coproduct.
	#########################################################

	global alpha1, alpha2

	if isinstance(o,L):
		return DeltaLnz(o.n, side)
	elif isinstance(o,G):

		if side == 'left':
			return DeltaGnTildeRidout(o.n-alpha2,side,1)
		if side == 'right':
			return DeltaGnTildeRidout(o.n-alpha1,side,1)

	

"""

def DeltaLn(n, side):
	h=2																				 # Virasoro conf dim
	M=10																			 # Upper Limit of sum
	out = []
	
	if n>=1-h:
		for m in range(1-h,n+1):
			out.append(binomial(n+h-1, m+h-1)*tensor(op([L(m)]),op([])))		
			
		if side=='left':
			return [tensor(op([]),op([L(n)]))] + out
		elif side=='right':
			return out + [tensor(op([]),op([L(n)]))]
			
	elif side == 'left':
		for m in range(1-h,M):
			out.append(binomial(m-n-1, -n-h)*(-1)**(n+h-1)*tensor(op([]), op([L(m)])))
		out.append(tensor(op([L(n)]),op([])))
			
	elif side == 'right':
		for m in range(1-h,M):
			out.append(binomial(m-n-1, -n-h)*(-1)**(m+h-1)*tensor(op([L(m)]),op([])))
		out.append(tensor(op([]),op([L(n)])))
   			
	return out
	
	
	
def DeltaGn(n, side):

	h=3/2																			 # SuperField conf dim
	M=10																			 # Upper Limit of sum
	out = []
	
	if n>=1-h:

		if side == 'left':
			for m in [i-1/2 for i in range(n+1)]:
				out.append(binomial(n+h-1, m+h-1)*tensor(op([G(m)]),op([])))		
			
			return [tensor(op([eps()]),op([G(n)]))] + out + [tensor(op([G(n)]),op([]))] 

		elif side=='right':
			for m in [i-1/2 for i in range(n+1)]:
				out.append(binomial(n+h-1, m+h-1)*tensor(op([G(m)]),op([])))	
	
			return [tensor(op([G(n)]),op([]))] + out + [tensor(op([eps()]),op([G(n)]))]
			
	elif side == 'left':
		for m in [i-1/2 for i in range(M)]:
			out.append(binomial(m-n-1, -n-h)*(-1)**(n+h-1)*tensor(op([eps()]), op([G(m)])))
		out.append(tensor(op([G(n)]),op([])))
			
	elif side == 'right':
		for m in [i-1/2 for i in range(M)]:
			out.append(binomial(m-n-1, -n-h)*(-1)**(m+h-1)*tensor(op([G(m)]),op([])))
		out.append(tensor(op([eps()]),op([G(n)])))
		
	return out
	


	

def Delta(o, side, N):
		
	###############################################################
	# Untwisted coproduct routing
	###############################################################
		
	if isinstance(o,L):
		return DeltaLn(o.n, side)
	elif isinstance(o,G):
		return DeltaGn(o.n,side)
"""		
		
def ListSum(o, depth):
		
	###################################################################
	# When the coproduct is less than the depth we cannot set it to zero
	# and must use the following sum instead
	###################################################################
	

	z = var('z')

	global alpha1, alpha2
		
	out = []
	o1 = copy.deepcopy(o)
	m = -o1.n + alpha2
	l = m	
	if isinstance(o,G):
		#if (2*m)%2==1:		
			# NEVEU SCHWARZ MODES
			# h = 3/2
			# while l <= depth:
				#####################################################################
				# We need the 'right' coproduct to have epsilon in the correct place
				# So we multiply through by epsilon accordingly.
				######################################################################
			#	o1.n = -l												
			#	out+=[binomial(l-h,m-h)*j for j in Delta(o1,'right',depth)]
			#	l+=1
		
		
				
		h = 3/2
		j = 0
		k = 0
		d = depth - l - alpha2
		while j + k<= depth:
			for j in range(0,d-k+1):
				o1.n = -l-j-k
				#print binomial(l+k-h-alpha2,k)*binomial(alpha1, j)*z**(k+j)*(-1)**(j), o1.n
				out+=[binomial(l+k-h-alpha2,k)*binomial(alpha1, j)*z**(k+j)*(-1)**(j)*x  for x in DeltaGnTildeRidout(o1.n,'right',depth)]
			k += 1
			j = 0
		
		#else:
			# print 'in the ramond sector of ListSum', o
			# RAMOND MODES
		#	h = 3/2
		#	j = 0
		#	k = 0
		#	d = depth - l - alpha2
		#	while j + k<= depth:
		#		for j in range(0,d-k+1):
		#			o1.n = -l-j-k
					#print o1, k, j
		#			out+=[binomial(-alpha2,k)*binomial(alpha1, j)*z**(k+j)*(-1)**(j)*x  for x in Delta(o1,'right',depth)]
		#		k += 1
		#		j = 0
						
		
	else:	
		# VIRASORO MODES	
		h = 2
		while l <= depth:
			o1.n = -l
			out+=[binomial(l-h,m-h)*j for j in Delta(o1,'right',depth)]
			l+=1
	
	return out
			
def ProdList(a,b):
	out=[]	
	for i in a:
		for j in b:
			out.append(i*j)
	return out
			
def DeltaExpansion(d, side, depth):
	if len(d) ==0:
		return [tensor(op([]), op([]))]
	result=Delta(d[0], side, depth)
	for i in range(1, len(d)):
		result = ProdList(result, Delta(d[i], side, depth))
	return RemoveBrackets(result)









###############################################
# 
#		 Parity Parameters
#
###############################################
			
class eps:	
			
	def __repr__(self):
		return '+/-'
			
def RemoveEpsilon(field):

	if len(field.state)>0:
		if isinstance(field.state[-1],eps):
			del field.state[-1]
			return field
		else:
			return field
	else:	
		return field
			
def EpsilonTensList(fieldList, vec):
	out = []
	fip = fieldList*vec
	for f in fip:
		f.left = RemoveEpsilon(f.left)
		out.append(f)
	return RemoveBrackets(out)
			


def Alpha1(o):
	global alpha1
	if isinstance(o,L):
		return 0
	elif isinstance(o,G) and o.n!=0:
		return alpha1
	else:
		return 0





############################################################################################################
#
# 				This is the Nahm Gaberbdiel Kausch Algorithm
#
###########################################################################################################


def GFAlg(inp, svlgrade, svrgrade, svl, svr, depth, c, h1, h2, fusion_basis, out, s=None, spur_reln = None): #, prev_inp = None, prev_redinp = None):
	global lsector, rsector
	global alpha1, alpha2
	inp = ListTensRepr(inp,h1,h2)
	#print 'input is {}'.format(inp)
	#print
	#pdb.set_trace()
	for x in inp:
		
		###################### Check if this term has already been processed ############################
		
		#	if len(prev_inp)!=0 and x in prev_inp:
			
		#	ind = prev_inp.index(x)
									
		#	new_inp =  prev_redinp[ind]
			
		#	GFAlg(new_inp,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln, prev_inp, prev_redinp)
			
			
		if x in fusion_basis:
			
		########################## Check if state is spurious ######################################
					
			#else:
			#print '{} is in the fusion basis'.format(x)
			#print
			#pdb.set_trace()
			out.append(x)
		elif s!= None and x in s: 
			#print '{} is a spurious state'.format(x)
			#print
			#pdb.set_trace()			
			ind = s.index(x)
			
			p = copy.deepcopy(x)
			
			p.left.state = []
			
			p.right.state = []
			
			mult = p*spur_reln[ind]
			
			GFAlg(mult,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)			
		################################# Sub in Singular Vector ############################################
			
		elif lsector == 'r' and x.left.state[-len(svl[0][-1].left.state):] == svl[0][-1].left.state: #BOSONIC SINGULAR VECTOR RELATION
			#print 'x.left.state[-svlgrade:] == [L(-1)]*svlgrade', x			
			#print
			#pdb.set_trace()
			
			pre = copy.deepcopy(x)
			
			pre.left.state = x.left.state[:-len(svl[0][-1].left.state)]
			
			combo = MakeList(-1/svl[0][-1].coef()*pre*svl[0][:-1])
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif lsector == 'r' and x.left.state[-len(svl[1][-1].left.state):] == svl[1][-1].left.state: #FERMIONIC SINGULAR VECTOR RELATION
			#print 'x.left.state[-svlgrade-1:] == [L(-1)]*svlgrade + [G(0)]', x			
			#print
			#pdb.set_trace()
			
			pre = copy.deepcopy(x)
			
			pre.left.state = x.left.state[:-len(svl[1][-1].left.state)]
			
			combo = MakeList(-1/svl[1][-1].coef()*pre*svl[1][:-1])
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif lsector == 'v' and x.left.state[-svlgrade:] == [L(-1)]*svlgrade : 
			
			pre = copy.deepcopy(x)
			
			pre.left.state = x.left.state[:-svlgrade]
			
			combo = MakeList(pre*svl)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif type(svlgrade) is Rational and x.left.state[-ceil(svlgrade):] == [L(-1)]*ceil(svlgrade) : 
			#print 'left state of {} is s.v. of form L(-1)...'.format(x)
			#print
			#pdb.set_trace()
			# Account for L(-1)^n = G(-1/2)L(-1)^(n-1)G(-1/2)
													
			pre = copy.deepcopy(x)
			
			pre.left.state = x.left.state[:-ceil(svlgrade)]
			
			combo = MakeList(pre*tensor(op([G(-1/2)]),op([]))*svl)
		
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif type(svlgrade) is Rational and x.left.state[-int(svlgrade+1/2):] == [L(-1)]*(int(svlgrade-1/2)) + [G(-1/2)]:
			#print 'left state of {} is s.v. of form L(-1)... + G(-1/2)'.format(x)
			#print
			#pdb.set_trace()
			pre = copy.deepcopy(x)
			
			pre.left.state = x.left.state[:-(svlgrade+1/2)]
			
			combo = MakeList(pre*svl)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif type(svlgrade) is Integer and lsector == 'ns' and  x.left.state[-svlgrade:] == [L(-1)]*svlgrade:
			
			pre = copy.deepcopy(x)
			
			pre.left.state = x.left.state[:-svlgrade]
			
			combo = MakeList(pre*svl)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif type(svlgrade) is Integer and lsector == 'ns' and  x.left.state[-svlgrade-1:] == [L(-1)]*svlgrade + [G(-1/2)]:
		
			pre = copy.deepcopy(x)
			
			pre.left.state = x.left.state[:-svlgrade-1] + [G(-1/2)]
			
			combo = MakeList(pre*svl)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
	
		elif rsector == 'r' and x.right.state[-len(svr[0][-1].right.state):] == svr[0][-1].right.state: #BOSONIC SINGULAR VECTOR RELATION
			#print 'x.right.state[-svrgrade:] == [L(-1)]*svlgrade', x			
			#pdb.set_trace()
		
			pre = copy.deepcopy(x)
		
			pre.right.state = x.right.state[:-len(svr[0][-1].right.state)]
			
			combo = MakeList(-1/svr[0][-1].coef()*pre*svr[0][:-1])
		
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif rsector == 'r' and x.right.state[-len(svr[1][-1].right.state):] == svr[1][-1].right.state: #FERMIONIC SINGULAR VECTOR RELATION
			#print 'x.right.state[-svrgrade-1:] == [L(-1)]*svlgrade + [G(0)]', x			
			#pdb.set_trace()
		
			pre = copy.deepcopy(x)
		
			pre.right.state = x.right.state[:-len(svr[1][-1].right.state)]
		
			combo = MakeList(-1/svr[1][-1].coef()*pre*svr[1][:-1])
		
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)

		elif rsector == 'v' and x.right.state[-svrgrade:] == [L(-1)]*svrgrade:
			pre = copy.deepcopy(x)
			
			pre.right.state = x.right.state[:-svrgrade]
			
			combo = MakeList(pre*svr)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
				
		elif type(svrgrade) is Rational and x.right.state[-ceil(svrgrade):] == [L(-1)]*ceil(svrgrade):
			#print 'right state of {} is s.v. of form L(-1)...'.format(x)
			#print
			#pdb.set_trace()
			pre = copy.deepcopy(x)
			
			pre.right.state = x.right.state[:-ceil(svrgrade)]
			
			combo = MakeList(pre*tensor(op([]),op([G(-1/2)]))*svr)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
					
		elif type(svrgrade) is Rational and x.right.state[-int(svrgrade+1/2):] == [L(-1)]*(int(svrgrade-1/2)) + [G(-1/2)]:
			#print 'right state of {} is s.v. of form L(-1)... + G(-1/2)'.format(x)
			#print
			#pdb.set_trace()
			pre = copy.deepcopy(x)
			
			pre.right.state = x.right.state[:-(svrgrade+1/2)]
			
			combo = MakeList(pre*svr)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif type(svrgrade) is Integer and x.right.state[-svrgrade:] == [L(-1)]*svrgrade and rsector =='ns':
			
			pre = copy.deepcopy(x)
			
			pre.right.state = x.right.state[:-svrgrade]
			
			combo = MakeList(pre*svr)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
		elif type(svrgrade) is Integer and x.right.state[-svrgrade-1:] == [L(-1)]*svrgrade + [G(-1/2)] and rsector =='ns':
			
			pre = copy.deepcopy(x)
			
			pre.right.state = x.right.state[:-svrgrade-1] + [G(-1/2)]
			
			combo = MakeList(pre*svr)
			
			GFAlg(combo,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)
			
			

		###########################  Replace Terms on the Left ############################################
			
		elif len(x.left.state)!=0 and x.left.state[0] not in (G(-1/2),L(-1),L(0),G(0)):
			#print 'left state of {} is not in ssubsp, use coproduct'.format(x)
			#print
			#pdb.set_trace()

			post = copy.deepcopy(x)
			
			post.left.state = x.left.state[1:]
			
			coprod = Delta(x.left.state[0], 'left', depth)

			coprod_coeff = coprod[-1].coef()
		
			coprod = [-1*i for i in coprod[:-1]]

			if -x.left.state[0].n+alpha2 <=depth:
				
				#print 'left factor is less than  or equal to depth'				
			
				conjterms = ListSum(x.left.state[0], depth)
		
				coprod.extend(conjterms)	
			
			coprod_post = EpsilonTensList(coprod,post)
			
			x_out = [1/coprod_coeff*i for i in coprod_post]
			#pdb.set_trace()	
			# prev_inp.append(x)
			# prev_redinp.append(x_out)		
			GFAlg(x_out,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)


		############################## Replace terms on the right #############################################
					
		elif -1*sum(o.n - Alpha1(o) for o in x.right.state) > depth:
			#print 'right state of {} is greater than depth'.format(x)
			#print
			#pdb.set_trace()			
			
			post = copy.deepcopy(x)
						
			n = -x.right.state[0].n + Alpha1(x.right.state[0])
			i = 1
			
			while(n<=depth):
				n+=-x.right.state[i].n + Alpha1(x.right.state[i])
				i+=1
			
			#print i
			#pdb.set_trace()

			post.right.state = x.right.state[i:]
			coprod = DeltaExpansion(x.right.state[:i], 'right', depth)	
			coprod_post = EpsilonTensList(coprod,post)

			#print coprod_post
			#pdb.set_trace()

			x_out = [-1/coprod_post[-1].coef()*x.coef()*i for i in coprod_post[:-1]]
			
			#pdb.set_trace()			
				
			# prev_inp.append(x)
			# prev_redinp.append(x_out)
			# pdb.set_trace()
			GFAlg(x_out,svlgrade, svrgrade, svl, svr, depth, c,h1, h2, fusion_basis, out, s, spur_reln)# prev_inp, prev_redinp)					 
			
		else:
			print 'WHAT IS THISSSS'
			print x
			pdb.set_trace()
			
	return out
		




	


########################################################################################################## 
#  
#     						Find Spurious Relations 
#
##########################################################################################################

def Spur((r1,s1),(r2,s2), depth, c,h1,h2,svl,svr,fusion_basis,spur_state_num, coprod_term = None, counter = 0,dstep=0,s_out=None,spur_reln_out=None):
	global lsector, rsector
	#(r2,s2) = (2,1)	####### FOR THE RAMOND/RAMOND CALCS I'VE SET THIS TO (2,1) SO WE DON'T SEARCH DEEPER THAN DEPTH 1	
	svlgrade = r1*s1/2
	svrgrade = r2*s2/2
		
	############################################
	# Sage treats a/b*b as a Rational so fix here
	############################################
	if svlgrade*2%2 == 0:
		svlgrade = Integer(svlgrade)
	if svrgrade*2%2 == 0:
		svrgrade = Integer(svrgrade)
		
		
	bstep = 0
		
	if s_out is None:
		s_out = []
	if spur_reln_out is None:
		spur_reln_out = []
		
	############################################################
	# We need to make sure what we are setting to zero is actually zero
	# So here we divide the two cases svgrade <> depth
	################################################################
	if svrgrade>depth:
		diff = 0
	else:
		if rsector == 'ns':
			diff = depth - svrgrade + 1/2		
		else:
			diff = ceil(depth) - svrgrade + 1
		
	############################################################
	# This loop will plug descendents of L_{-1}^(svrgrade) acting on basis elts
	# into the alg and see if anything non-zero comes out. If yes then this will
 	# be added to the fusion calc as a spurious state
	#########################################################
		
	if coprod_term is None:
		if rsector == 'ns':
			coprod_term = [L(-1)]*floor(svrgrade + diff+dstep) + [G(-1/2)]*((svrgrade + diff+dstep)*2%2)
			counter = len(MakeBasis(svrgrade + diff+dstep,'ns'))
		elif rsector == 'r':
			coprod_term = MakeBasis(svrgrade + diff+dstep,'r')[0][-1].state #[L(-1)]*floor(svrgrade + diff+dstep) 
			counter = len(MakeBasis(svrgrade + diff+dstep,'r')[0])

	while len(s_out)< spur_state_num:
	
		basis_elt = fusion_basis[bstep]
		#pdb.set_trace()
		spurious = GFAlg(EpsilonTensList(DeltaExpansion(coprod_term,'right',depth),basis_elt),svlgrade, svrgrade, svl, svr, depth, c, h1, h2, fusion_basis, [], s_out, spur_reln_out)
		#DavidTerms = [tensor(op([L(-1)]),op([])), 1/2*tensor(op([]),op([G(-1),G(0)])),1/2*tensor(op([]),op([G(0),G(-1)]))]
		#spurious = GFAlg(EpsilonTensList(DeltaExpansion(coprod_term,'right',10),basis_elt),svlgrade, svrgrade, svl, svr, depth, c, h1, h2, fusion_basis, [], s_out, spur_reln_out)
		
		spur_reln = copy.deepcopy(fusion_basis)
			
		for u in spur_reln:
			
			u.coeff = 0
			
		for t in spurious:
			
			spur_reln[fusion_basis.index(t)].coeff+=t.coef()
			
			
		spur_reln = ListTensRepr(spur_reln, h1, h2)
		
		if len(spur_reln)==1:
			spur_reln_out.append([])
			spur_reln[0].coeff = 1
			s_out.append(spur_reln[0])
			fusion_basis.remove(spur_reln[0])
			print (svrgrade + diff + dstep, bstep), coprod_term, 'acting on', basis_elt
			print
			print 'SPURIOUS: {} = {}'.format(spur_reln[0], 0)
			print
			if bstep < len(fusion_basis) -1:
				bstep+=1
			else:
				bstep=0
				if rsector =='ns':
					dstep+=1/2
				#else:
				#	dstep+=1
		elif len(spur_reln)>1:
			s = spur_reln[-1]
			spur_reln = [-1/s.coef()*i for i in spur_reln[:-1]]
			s.coeff = 1
			spur_reln_out.append(spur_reln)
			s_out.append(s)
			fusion_basis.remove(s)
			print (svrgrade + diff + dstep, bstep), coprod_term, 'acting on', basis_elt
			print
			print 'SPURIOUS: {} = {}'.format(s, spur_reln)
			print
			#pdb.set_trace()
			if bstep < len(fusion_basis) -1:
				bstep+=1
			else:
				bstep=0
				if rsector =='ns':
					dstep+=1/2
				#else:
				#	dstep+=1
		else:	 
			print
			print  (svrgrade + diff + dstep, bstep), coprod_term, 'acting on', basis_elt, 'gives', []
			print
			cont = str(raw_input('continue(c)/quit(q)/new coprod(n)/old coprod(o)? '))
			if cont == 'q':
				return fusion_basis, s_out, spur_reln_out
			elif cont == 'o':

				if rsector == 'ns':
					if counter !=0:
					 	counter-=1
					else:
						dstep-=1/2
						counter = len(MakeBasis(svrgrade + diff + dstep,'ns'))-1
					
					#coprod_term =  MakeBasis(svrgrade + diff + dstep,'ns')[counter].state

				elif rsector == 'r':
					if counter !=0:
					 	counter-=1
					else:
						dstep-=1

						counter = len(RemoveBrackets(MakeBasis(svrgrade + diff + dstep,'r')))-1
					coprod_term =  RemoveBrackets(MakeBasis(svrgrade + diff + dstep,'r'))[counter].state

				Spur((r1,s1),(r2,s2), depth, c,h1,h2,svl,svr,fusion_basis,spur_state_num, coprod_term,counter,dstep,s_out,spur_reln_out)	
				break	
			elif cont == 'n':
				if rsector == 'r':
					if counter < len(RemoveBrackets(MakeBasis(svrgrade + diff + dstep,'r'))) -1:
				 		counter +=1
					else:
						dstep+=1
						counter == 0
				
					coprod_term =  RemoveBrackets(MakeBasis(svrgrade + diff + dstep,'r'))[counter].state
			 		
				elif rsector == 'ns':
					if counter < len(MakeBasis(svrgrade + diff + dstep,'ns')) -1:
				 		counter +=1
					else:
				 		dstep+=1/2
				 		counter == 0
				
					coprod_term =  MakeBasis(svrgrade + diff + dstep,'ns')[counter].state
				
				Spur((r1,s1),(r2,s2), depth, c,h1,h2,svl,svr,fusion_basis,spur_state_num, coprod_term,counter,dstep,s_out,spur_reln_out)	
				break		
			elif cont == 'c':
				if bstep < len(fusion_basis) -1:
					bstep+=1
				else:
					bstep=0
					if rsector =='ns':
						dstep+=1/2
					#else:
					#	dstep+=1
						
	
	
	print 'done'
	return fusion_basis, s_out, spur_reln_out






			
#################################################################################################
#
#				Calculate Each Representating Matrix
#
#################################################################################################
			
def DeltaMatrix(o, svlgrade, svrgrade,svl, svr, depth, c, h1, h2, fusion_basis, s_out, spur_reln_out):
	print o	
	
	Matrix = [[0]*len(fusion_basis) for i in fusion_basis]
			
	row=0	
	i = 1
	for x in fusion_basis:
		
		print 'NEW STATE COMING IN WOOO -- ',x,' (', i, ' OF ', len(fusion_basis), ')'

		mult = EpsilonTensList(Delta(o, 'left',depth),x)
			
		mult = RemoveBrackets(mult)
			
		mult = ListTensRepr(mult, h1, h2)
			
		proc =  GFAlg(mult,svlgrade, svrgrade, svl, svr, depth, c, h1, h2, fusion_basis,[], s_out, spur_reln_out)
			
		for item in proc:
			
			col = fusion_basis.index(item)
			
			Matrix[row][col] += item.coef()
   		
		row+=1
		i+=1
	A = matrix(Matrix)
	#print fusion_basis
	return A.transpose()
			




			
#############################################################################################
#
# 						Input parameters
#
##############################################################################################			
			
start = time()
			
lsector = str(raw_input('lsector: '))
rsector = str(raw_input('rsector: '))
#c= Rational(raw_input('c: '))
t_value = Rational(raw_input('t_value: '))
alpha1 = Rational(raw_input('alpha1: '))
alpha2 = Rational(raw_input('alpha2: '))

c = 15/2-3*(t_value+1/t_value)


def ConfWeight((r,s),sector):
	global t_value
	if sector == 'v':
		return 	((r - t_value*s)**2  - (1-t_value)**2)/4/t_value
	elif sector == 'ns':
		return	((r - t_value*s)**2  - (1-t_value)**2)/8/t_value
	elif sector == 'r':
		return	((r - t_value*s)**2  - (1-t_value)**2)/8/t_value + 1/16



###########################################################################################3
#
#                 			Minimal Model Fusion Rules
#
##############################################################################################

def frule((p1,q1),(p2,q2)):
	out = []
	for i in range(abs(p1-p2)+1,p1+p2,2):
		for j in range(abs(q1-q2)+1,q1+q2,2):
			out.append((i,j))
	return out





##############################################################################################
#
#                            Beta
#
##############################################################################################

def AdSingVec(svgrade,hw,sector):
	iden = op([])
	out = iden
	starting_state = MakeBasis(svgrade,sector)[-1].state
	starting_state.reverse()
	for i in starting_state:
		i.n *=-1
		out*= op([i])
	
	out = [out]

	for v in SingVec(svgrade,hw,sector):
		pre_out = iden
		v.state.reverse()
		for i in v.state:
			i.n*=-1
			pre_out *= op([i])
		out+= [-1*v.coeff*pre_out]
	return out

def FullSingVec(svgrade,hw,sector):
	out = []
	starting_state = MakeBasis(svgrade,sector)[-1]
	out.append(starting_state)

	for v in SingVec(svgrade,hw,sector):
		out+= [-1*v]
	return out

def beta((r,s),(u,v)):
	global t_value
	global c
	global lsector, rsector
	originalc = copy.deepcopy(c)
	e = var('e')
	denom = (u**2 - r**2)/8/t_value**2 -(v**2-s**2)/8
	A = FullSingVec(Rational(ConfWeight((u,v),rsector)-ConfWeight((r,s),lsector)),ConfWeight((r,s),lsector),lsector)
	A_dag = AdSingVec(Rational(ConfWeight((u,v),rsector)-ConfWeight((r,s),lsector)),ConfWeight((r,s),lsector),lsector)
	c = c - 3*(1-1/t_value**2)*e
	num = RemoveBrackets(ListTensRepr(tensor(ProdList(A_dag,A),op([])), ConfWeight((r,s),lsector)+((s**2-1)/8-(r**2-1)/8/t_value**2)*e,0))#[0][0].coef()
	#print num
	b= 0
	for i in num:
		b+=diff(i.coef(),e)/denom

	c = originalc
	return b
	#b = diff(num,e)/denom
	#return b

###############################################################################################
#
# 						Calculate All Matrices
#
#################################################################################################


def Matrices((r1,s1),(r2,s2), depth):
	
	z_value = 1

	global c, t_value

	global lsector, rsector
	
	global alpha1, alpha2

	if lsector in ('ns','r'):
		svlgrade = r1*s1/2
	elif lsector == 'v':
		svlgrade = r1*s1

	if rsector in ('ns','r'):
		svrgrade = r2*s2/2	
	elif rsector == 'v':
		svrgrade = r2*s2
	
	h1 = ConfWeight((r1,s1),lsector)
	h2 = ConfWeight((r2,s2),rsector)

	############################################
	# Sage treats a/b*b as a Rational so fix here
	############################################
	if svlgrade*2%2 == 0:
		svlgrade = Integer(svlgrade)
	if svrgrade*2%2 == 0:
		svrgrade = Integer(svrgrade)

	fusion_basis = FusionBasis((r1,s1),(r2,s2),depth)

	s=[]

	for i in fusion_basis:
       		if i not in s:
          		s.append(i)		
	
	fusion_basis = s	

	left_dim = len(fusion_basis)
	
	right_dim = 0
	
	if lsector == 'v' and rsector == 'v':
		for (a,b) in frule((r1,s1),(r2,s2)):
			right_dim += len(FusionBasis((1,1),(a,b),depth))
	elif lsector == 'r' and rsector == 'r':
		for (a,b) in frule((r1,s1),(r2,s2)):
			right_dim += 2*len(FusionBasis((1,1),(a,b),depth))
	elif lsector == 'ns' and rsector == 'ns':
		for (a,b) in frule((r1,s1),(r2,s2)):
			right_dim += len(FusionBasis((1,1),(a,b),depth))
	elif lsector == 'ns' and rsector == 'r':
		for (a,b) in frule((r1,s1),(r2,s2)):
			right_dim += len(FusionBasis((1,1),(a,b),depth))
	elif lsector == 'r' and rsector == 'ns':
		for (a,b) in frule((r1,s1),(r2,s2)):
			right_dim += len(FusionBasis((1,1),(a,b),depth))
	else:
		print "Don't have the fusion rules"
		return
	
	spur_state_num =  left_dim - right_dim
	
	print spur_state_num, 'spurious state(s)'
	
	if lsector == 'r':
		svl = [tensor(SingVec(svlgrade,h1,lsector)[0],op([]))] + [tensor(SingVec(svlgrade,h1,lsector)[1],op([]))] 
	else:
		svl = tensor(SingVec(svlgrade,h1,lsector),op([]))
		
	if rsector == 'r':
		svr = [tensor(op([]), SingVec(svrgrade,h2,rsector)[0])] + [tensor(op([]), SingVec(svrgrade,h2,rsector)[1])]
	else:
		svr = tensor(op([]), SingVec(svrgrade,h2,rsector))
	
		

	
	fusion_basis, s_out, spur_reln_out = Spur((r1,s1),(r2,s2),depth,c,h1,h2,svl,svr,fusion_basis, spur_state_num)
	
	#fusion_basis = [tensor(op([]),op([])), tensor(op([G(0)]),op([])), tensor(op([]),op([G(-1/2)])),tensor(op([G(0)]),op([G(-1/2)]))]

	bos_basis = []
	ferm_basis = []
	for f in fusion_basis:
		b = f.left.state + f.right.state
		if sum(isinstance(i,G) for i in b)%2==0:
			bos_basis.append(f)
		else:
			ferm_basis.append(f)
	
	fusion_basis = bos_basis + ferm_basis
	


	#s_out, spur_reln_out = [], []

	M = {}	
	M['L0'] = DeltaMatrix(L(0),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)

	#return M['L0']
	if type(M['L0']) == sage.matrix.matrix_symbolic_dense.Matrix_symbolic_dense:
		M['L0'] = matrix(QQ,M['L0'](z=z_value,t=t_value))
	K = M['L0'].jordan_form(transformation = true)
	J = K[0]
	P = K[1]
	print 'J,P done'
	print time() - start

	#M['G0'] = DeltaMatrix(G(0),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)
	#print 'G0 done'
	#print time() - start
		
	for i in range(1, depth+1):

		A = DeltaMatrix(L(-i),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)
	
		if type(A) == sage.matrix.matrix_symbolic_dense.Matrix_symbolic_dense:
			M['L({})'.format(-i)] = matrix(QQ, A(z=z_value, t = t_value))
		else:
			M['L({})'.format(-i)]= A
	
		print 'L({}) done'.format(-i)
		print time() - start
		
		B = DeltaMatrix(L(i),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)

		if type(B) == sage.matrix.matrix_symbolic_dense.Matrix_symbolic_dense:
			M['L({})'.format(i)] = matrix(QQ, B(z=z_value, t = t_value))
		else:
			M['L({})'.format(i)] = B

		print 'L({}) done'.format(i)
		print time() - start

		
			
	if lsector=='ns' and rsector == 'ns':
		for i in range(1, depth+3/2):
			i-=1/2

			A = DeltaMatrix(G(-i),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)

			print 'G({}) done'.format(-i)
			print time() - start

			B = DeltaMatrix(G(i),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)

			print 'G({}) done'.format(i)
			print time() - start

			if type(A) ==  sage.matrix.matrix_symbolic_dense.Matrix_symbolic_dense:
				M['G({})'.format(-i)] = matrix(QQ, A(z=z_value, t = t_value))
			else:
				M['G({})'.format(-i)] = A

			if type(B) ==  sage.matrix.matrix_symbolic_dense.Matrix_symbolic_dense:
				M['G({})'.format(i)] = matrix(QQ, B(z=z_value, t = t_value))
			else:
				M['G({})'.format(i)] = B

	if lsector=='r' and rsector == 'r':
		for n in range(-depth, depth+1/2):
			n+=1/2

			M['G({})'.format(n)]  = DeltaMatrix(G(n+alpha1),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)

			print 'G({}) done'.format(n)
			print time() - start

			##################### Here we switch from Tilde to Non-Tilde Modes ###########################

			for j in range(1,n+depth+1):
				M['G({})'.format(n)] += binomial(alpha1,j)*(-z)**j*M['G({})'.format(n-j)] 					

	if lsector=='ns' and rsector == 'r':
		for n in range(-depth, depth + 1):
			
			M['G({})'.format(n)]  = DeltaMatrix(G(n),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)

			print 'G({}) done'.format(n)
			print time() - start

			##################### Here we switch from Tilde to Non-Tilde Modes ###########################

			for j in range(1,n+depth+1):
				M['G({})'.format(n)] += binomial(alpha1,j)*(-z)**j*M['G({})'.format(n-j)] 	
	

	if lsector=='r' and rsector == 'ns':
		for n in range(-depth, depth + 1):
			
			M['G({})'.format(n)]  = DeltaMatrix(G(n),svlgrade, svrgrade, svl, svr, depth,0,h1,h2, fusion_basis, s_out, spur_reln_out)

			print 'G({}) done'.format(n)
			print time() - start

			##################### Here we switch from Tilde to Non-Tilde Modes ###########################

			for j in range(1,n+depth+1):
				M['G({})'.format(n)] += binomial(alpha1,j)*(-z)**j*M['G({})'.format(n-j)] 	
	

	return J,P,M
	#return M
	
#########################################################################
#
# 				Post Calculation Analysis
#
###########################################################################

def MSV(svgrade,hw,sector):
	iden = identity_matrix(len(J[0]))
	out = iden
	for i in MakeBasis(svgrade,sector)[-1].state:
		out*= M['{}'.format(i)]

	for v in SingVec(svgrade,hw,sector):
		pre_out = iden
		for i in v.state:
			pre_out *= M['{}'.format(i)]
		out-= v.coeff*pre_out
	return out

def AdMSV(svgrade,hw,sector):
	iden = identity_matrix(len(J[0]))
	out = iden
	starting_state = MakeBasis(svgrade,sector)[-1].state
	starting_state.reverse()
	for i in starting_state:
		i.n *=-1
		out*= M['{}'.format(i)]
	
	for v in SingVec(svgrade,hw,sector):
		pre_out = iden
		v.state.reverse()
		for i in v.state:
			i.n*=-1
			pre_out *= M['{}'.format(i)]
		out-= v.coeff*pre_out
	return out


