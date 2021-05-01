def solo_prod_list(l,K,d):
    r"""
    INPUT: K a ring of polynomials, l=[a_1,...,a_m] a list of elements in
    the base ring of K of length at least d, and d an integer.
    OUTPUT: (X-a_1)(X-a_2)...(X-a_d) in K.

    This algorithm uses a divide and conquer method.

    EXAMPLES:
        sage: ZZY.<Y>=ZZ[]
        sage: solo_prod_list([1,2,3,4],ZZY,4)
        Y^4 - 10*Y^3 + 35*Y^2 - 50*Y + 24

        sage: F5Y.<Y>=ZZ[]
        sage: solo_prod_list([0,2,3],F5Y,3)
        Y^3 + Y
    """
    if d==1:
        return(K([-l[0],1]))
    else:
        n=d//2
        P1=solo_prod_list(l[:n],K,n)
        P2=solo_prod_list(l[d//2:],K,d-n)
        return(P1*P2)

def solo_change_basis(P,l,K):
    r"""
    INPUT: P=[a_0,a_1,...,a_m] and l=[l_0,l_1,...,l_n] two list of
    coefficient in the base ring of K, with l of length greater than P, K a
    ring of polynomials.
    OUTPUT: a_m(X-l_0)(X-l_1)...(X-l_{m-1})+...+a_1(X-l_0)+a_0

    The algorithm uses a divide and conquer method.

    EXAMPLES:

        sage: ZZY.<Y>=ZZ[]
        sage: solo_change_basis([1],[2,3],ZZY)
        1

        sage: solo_change_basis([1,2],[2],ZZY)
        2*X-3

        sage: solo_change_basis([2,1,-1],[-1,1],ZZY)
        -Y^2 + Y + 4
    """
    n=len(P)
    if n==0:
        return(0)
    if n==1:
        return(P[0])
    d=n//2
    P1=P[:d]
    P2=P[d:]
    Q1=solo_change_basis(P1,l[:d-1],K)
    Q2=solo_change_basis(P2,l[d:],K)
    Q3=solo_prod_list(l[:d],K,d)
    return(Q1+Q3*Q2)

def solo_relevant_translation( L, p ):
    r"""
    INPUT: A list L of polynomial with coefficients in a ring.
    OUTPUT: The same translated by a where a is the smallest positive or
    null integer to not be a root of L[-1], and a

    WARNING: If used on a ring of positive characteristic and L[-1] is zero
    over the image of ZZ, then the fonction won't terminate.

    EXAMPLES:
        sage: ZZY.<Y>=ZZ[]
        sage: L=[-Y^2 - 1, Y^2 - Y - 4, -Y^2 + 2*Y - 4]
        sage: solo_relevant_translation(L)
        ([-Y^2 - 1, Y^2 - Y - 4, -Y^2 + 2*Y - 4], 0)

        sage: L=[-Y^2 - 1, Y^2 - Y - 4, Y^3 - 3*Y^2 + 2*Y]
        sage: solo_relevant_translation(L)
        ([-Y^2 - 6*Y - 10, Y^2 + 5*Y + 2, Y^3 + 6*Y^2 + 11*Y + 6], 3)
    """
    L1 = [ ]
    P = L[ -1 ]
    K=P.parent()
    i = 0
    while P(i)%p == 0:
        i=i+1
    if i != 0:
        for P in L:
            L1.append( P( K( [i,1] ) ) )
        return(L1,i)
    else:
        return(L,i)

def solo_isomorphism(L,d):
    r"""This fonction computes the solo_isomorphism of Ore polynomials algebra
    of differential operator represented by a list of polynomials. This
    transformation algorithm rely on the following principle :
    If L is given by L=l_m x^m d^m+...+l_1 x d+l_0 then the image of L by
    the solo_isomorphism is given by
    phi(L)=l_m x(x-1)(x-2)...(x-m+1)+...+l_2 x(x-1)+ l_1 x + l_0
    
    EXAMPLES : 
        sage: ZZY.<Y>=ZZ[]
        sage: L=[13*Y^2 + 2*Y + 1, -4*Y^2 + 2*Y, -Y^2 - 6*Y, Y^2 + 2*Y + 2]
        sage: solo_isomorphism(L)
        ([13*Y^2 - 13*Y, -4*Y^2 + 6*Y, -Y^2 + 3*Y + 1, Y^2 - 7*Y, 2*Y, 2], 2)
        
        sage: L=[-17*Y^4 + 6*Y^3 + Y^2 - 3, -6*Y^4 + 2*Y^3 + 11*Y + 1,
        Y^4 + Y^3 + Y^2 + Y - 1, Y^4 - Y - 1]
        sage: solo_isomorphism(L)
        ([-17*Y^4 + 102*Y^3 - 187*Y^2 + 102*Y,-6*Y^4 + 42*Y^3 - 84*Y^2
        +48*Y, Y^4 - 4*Y^3 + 6*Y^2 - 3*Y, Y^4 - 5*Y^3 + 8*Y^2 - 4*Y,
        Y^2 + 10*Y - 3, Y + 1, -Y - 1, -1], 4)
    """
    K=L[0].parent()
    m=len(L)
    L1=[]
    bases=[i for i in range(1,d)]
    for i in range(-d,m):
        l=[0 for j in range(0,-i)]
        for j in range(max(0,-i),min(d+1,m-i)):
            P=L[i+j]
            if P.degree()>=j:
                l.append(P[j])
            else:
                l.append(0)
        aj=l[0]+K([0,1])*solo_change_basis(l[1:],bases,K)
        L1.append(aj)
    puiss=d
    while L1[0]==0 and puiss>0:
        L1.pop(0)
        puiss+=-1
    while L1[-1]==0:
        L1.pop(-1)
    return(L1,puiss)

def solo_build_matrix(L,m, p):
    r"""
    INPUT: A list L of element of a ring representing a polynomial, m the
    length of L.
    OUTPUT: What would be L[-1] times the companion matrix of L if L[-1]
    were invertible

    EXAMPLES:
        sage: L=[-1, 0, -25, -2, 2]
        sage: solo_build_matrix(L,5)
        [ 0  0  0  1]
        [ 2  0  0  0]
        [ 0  2  0 25]
        [ 0  0  2  2]

        sage: Z4=IntegerModRing(4)
        sage: L=[Z4(3),Z4(0),Z4(1),Z4(2),Z4(1),Z4(2)]
        sage: solo_build_matrix(L,6)
        [0 0 0 0 1]
        [2 0 0 0 0]
        [0 2 0 0 3]
        [0 0 2 0 2]
        [0 0 0 2 3]
        
        sage: solo_build_matrix(L,6).parent()
        Full MatrixSpace of 5 by 5 dense matrices over Ring of integers modulo 4
    """
    FpY.<Y>=GF(p)[]
    coeff=L[-1]
    M=[]
    ligne=[0 for i in range(m-2)]
    ligne.append(FpY(-L[0]))
    M.append(ligne)
    for j in range(m-2):
        ligne=[0 for i in range(j)]
        ligne.append(FpY(coeff))
        ligne=ligne+[0 for i in range(m-j-3)]
        ligne.append(FpY(-L[j+1]))
        M.append(ligne)
    return(matrix(M))

def solo_prod(L):
    l=len(L)
    if l==0:
        return(1)
    if l==1:
        return(L[0])
    L1=L[:l//2]
    L2=L[l//2:]
    return(solo_prod(L1)*solo_prod(L2))

def solo_compute_factorial( M, p, d):
    K=M[0,0].parent()
    Ky.<Y>=K.base_ring()[[]]
    rp=int(sqrt(p))
    L=[M(K([i,1])) for i in range(rp)]
    Bp=solo_prod(L)
    eta=0
    n=1
    while n<rp:
        eta+=1
        n=n*2
    Prod_tree=[[1 for j in range(2^i)] for i in range(eta+1)]
    k=0
    j=0
    while j<=2^eta-1:
        if k*2^eta<=(j*rp):
            Prod_tree[eta][j]=K([-rp*k,1])^(d+1)
            k+=1
        j+=1
    for i in range(1,eta+1):
        for j in range(2^(eta-i)):
            Prod_tree[eta-i][j]=Prod_tree[eta-i+1][2*j]*Prod_tree[eta-i+1][2*j+1]
    res_tree=[[1 for j in range(2^i)] for i in range(eta+1)]
    res_tree[0][0]=Bp%Prod_tree[0][0]
    for i in range(1,eta+1):
        for j in range(2^i):
            res_tree[i][j]=res_tree[i-1][j//2]%Prod_tree[i][j]
    j=0
    liste_bpp=[]
    for i in range(2^eta):
        if Prod_tree[eta][i]!=1:
            liste_bpp.append(((res_tree[eta][i])(K([j*rp,1]))).change_ring(Ky))
            j+=1
    MgrO=matrix([[O(Y^(d+1)) for i in range(M.dimensions()[1])] for j in range(M.dimensions()[0])])
    liste_bpp=[B+MgrO for B in liste_bpp]
    lqdsf=[K([-i*rp,1])^(d+1) for i in range(rp)]
    Bp=solo_prod(liste_bpp)
    for i in range(rp*rp,p):
        Bp=Bp*M(K([i,1]))
    return(Bp)

def solo_adding( l , i, j, a ):
    r"""
    This function adds a coefficient a to a list representing a polynomial
    over two variables, so that a is added to the coefficient of x^i Y^j
    
    EXAMPLES:
        sage: L=[[0]]
        sage: solo_adding(l,2,3,1)
        sage: l
        [[0],[0],[0,0,0,1]]
        sage: solo_adding(l,2,3,1)
        sage: l
        [[0],[0],[0,0,0,2]]
        sage: solo_adding(l,1,0,-1)
        sage: l
        [[0], [-1], [0, 0, 0, 2]]
    """
    
    length=len(l)
    for i1 in range( i-length+1 ):
        l.append([0])
    width=len(l[i])
    for j2 in range( j-width+1 ):
        l[i].append(0)
    l[i][j] = l[i][j]+a

def solo_reverse_iso( P, p, borne ):
    r"""
    This function computes the reverse solo_isomorphisme of Ore polynomials
    algebra of P assmuming that P has its coefficients in GF(p)[Y^p-Y] and
    of degree less than borne*p.
    It returns the result in the form a list of coefficients in GF(p).
    """
    l = [ [ 0 ] ]
    L = P.list()
    d=P.degree()
    for i in range( d+1 ):
        a = L[i].list()
        lim = min(len(a),borne)
        coeff = 1
        for j in range( lim ):
            to_add = a[ j ]
            if to_add != 0:
                solo_adding( l, i+j, j, coeff*to_add )
            coeff = -1*coeff
    return(l)
    
    

def solo_p_curvature(L,p):
    K=L.parent()
    BR=K.base_ring()
    variable=BR.variable_name()
    ZZY=ZZ[variable]
    if BR != ZZY and K.twisting_derivation() != ZZY.derivation():
        raise NotImplementedError
    coefficients_list=L.list()
    L2, trans_reminder = solo_relevant_translation( coefficients_list, p )
    d = max( P.degree() for P in L2 )
    L1, denom = solo_isomorphism( L2, d )
    m = len( L1 )
    coeff = GF(p)(L1[ -1 ])
    M = solo_build_matrix( L1, m, p )
    Bp = solo_compute_factorial( M, p, d )
    Bp=Bp/coeff
    print(Bp)
    xi_theta=coeff*Bp.charpoly()
    FpY=GF(p)[variable]
    xi_theta=xi_theta.change_ring(FpY)
    xi_x=solo_reverse_iso(xi_theta,p,d+1)
    leading_coeff=FpY(L[-1])
    l=[]
    for i in range(len(xi_x)):
        pre_trans = FpY(xi_x[i])
        if trans_reminder != 0:
            pre_trans=pre_trans(FpY([-trans_reminder,1]))
        l.append(pre_trans)
    if variable != 'x' and variable != 'X':
        FpYx.<X>=FpY[ ]
    else:
        FpYx.<Y>=FpY[ ]
    l=FpYx(l[ denom : ])
    return(l/leading_coeff)

