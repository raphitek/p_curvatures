def relevant_translation( L ):
    r"""
    INPUT: A list L of polynomial with coefficients in a ring.
    OUTPUT: The same translated by a where a is the smallest positive or
    null integer to not be a root of L[-1], and a

    WARNING: If used on a ring of positive characteristic and L[-1] is zero
    over the image of ZZ, then the fonction won't terminate.

    EXAMPLES:
        sage: ZZY.<Y>=ZZ[]
        sage: L=[-Y^2 - 1, Y^2 - Y - 4, -Y^2 + 2*Y - 4]
        sage: relevant_translation(L)
        ([-Y^2 - 1, Y^2 - Y - 4, -Y^2 + 2*Y - 4], 0)

        sage: L=[-Y^2 - 1, Y^2 - Y - 4, Y^3 - 3*Y^2 + 2*Y]
        sage: relevant_translation(L)
        ([-Y^2 - 6*Y - 10, Y^2 + 5*Y + 2, Y^3 + 6*Y^2 + 11*Y + 6], 3)
    """
    L1 = [ ]
    P = L[ -1 ]
    K=P.parent()
    i = 0
    while P(i) == 0:
        i+=1
    if i != 0:
        for P in L:
            L1.append( P( K( [i,1] ) ) )
        return(L1,i)
    else:
        return(L,i)

def prod_list(l,K,d):
    r"""
    INPUT: K a ring of polynomials, l=[a_1,...,a_m] a list of elements in
    the base ring of K of length at least d, and d an integer.
    OUTPUT: (X-a_1)(X-a_2)...(X-a_d) in K.

    This algorithm uses a divide and conquer method.

    EXAMPLES:
        sage: ZZY.<Y>=ZZ[]
        sage: prod_list([1,2,3,4],ZZY,4)
        Y^4 - 10*Y^3 + 35*Y^2 - 50*Y + 24

        sage: F5Y.<Y>=ZZ[]
        sage: prod_list([0,2,3],F5Y,3)
        Y^3 + Y
    """
    if d==1:
        return(K([-l[0],1]))
    else:
        n=d//2
        P1=prod_list(l[:n],K,n)
        P2=prod_list(l[d//2:],K,d-n)
        return(P1*P2)

def change_basis(P,l,K):
    r"""
    INPUT: P=[a_0,a_1,...,a_m] and l=[l_0,l_1,...,l_n] two list of
    coefficient in the base ring of K, with l of length greater than P, K a
    ring of polynomials.
    OUTPUT: a_m(X-l_0)(X-l_1)...(X-l_{m-1})+...+a_1(X-l_0)+a_0

    The algorithm uses a divide and conquer method.

    EXAMPLES:

        sage: ZZY.<Y>=ZZ[]
        sage: change_basis([1],[2,3],ZZY)
        1

        sage: change_basis([1,2],[2],ZZY)
        2*X-3

        sage: change_basis([2,1,-1],[-1,1],ZZY)
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
    Q1=change_basis(P1,l[:d-1],K)
    Q2=change_basis(P2,l[d:],K)
    Q3=prod_list(l[:d],K,d)
    return(Q1+Q3*Q2)

def isomorphism(L,d):
    r"""This fonction computes the isomorphism of Ore polynomials algebra
    of differential operator represented by a list of polynomials. This
    transformation algorithm rely on the following principle :
    If L is given by L=l_m x^m d^m+...+l_1 x d+l_0 then the image of L by
    the isomorphism is given by
    phi(L)=l_m x(x-1)(x-2)...(x-m+1)+...+l_2 x(x-1)+ l_1 x + l_0
    
    EXAMPLES : 
        sage: ZZY.<Y>=ZZ[]
        sage: L=[13*Y^2 + 2*Y + 1, -4*Y^2 + 2*Y, -Y^2 - 6*Y, Y^2 + 2*Y + 2]
        sage: isomorphism(L)
        ([13*Y^2 - 13*Y, -4*Y^2 + 6*Y, -Y^2 + 3*Y + 1, Y^2 - 7*Y, 2*Y, 2], 2)
        
        sage: L=[-17*Y^4 + 6*Y^3 + Y^2 - 3, -6*Y^4 + 2*Y^3 + 11*Y + 1,
        Y^4 + Y^3 + Y^2 + Y - 1, Y^4 - Y - 1]
        sage: isomorphism(L)
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
        aj=l[0]+K([0,1])*change_basis(l[1:],bases,K)
        L1.append(aj)
    puiss=d
    while L1[0]==0:
        L1.pop(0)
        puiss+=-1
    while L1[-1]==0:
        L1.pop(-1)
    return(L1,puiss)

def build_matrix(L,m):
    r"""
    INPUT: A list L of element of a ring representing a polynomial, m the
    length of L.
    OUTPUT: What would be L[-1] times the companion matrix of L if L[-1]
    were invertible

    EXAMPLES:
        sage: L=[-1, 0, -25, -2, 2]
        sage: build_matrix(L,5)
        [ 0  0  0  1]
        [ 2  0  0  0]
        [ 0  2  0 25]
        [ 0  0  2  2]

        sage: Z4=IntegerModRing(4)
        sage: L=[Z4(3),Z4(0),Z4(1),Z4(2),Z4(1),Z4(2)]
        sage: build_matrix(L,6)
        [0 0 0 0 1]
        [2 0 0 0 0]
        [0 2 0 0 3]
        [0 0 2 0 2]
        [0 0 0 2 3]
        
        sage: build_matrix(L,6).parent()
        Full MatrixSpace of 5 by 5 dense matrices over Ring of integers modulo 4
    """
    coeff=L[-1]
    M=[]
    ligne=[0 for i in range(m-2)]
    ligne.append(-L[0])
    M.append(ligne)
    for j in range(m-2):
        ligne=[0 for i in range(j)]
        ligne.append(coeff)
        ligne=ligne+[0 for i in range(m-j-3)]
        ligne.append(-L[j+1])
        M.append(ligne)
    return(matrix(M))

def fill(Ad,Sd,N,n,L,p_list):
    r"""
    INPUT: Ad and Sd are list filled with 1 of length n. N an integer. L a
    list and p_list and list of integer.

    This functions fills Ad with elements of L and Sd with elements of
    p_list.
    The filling rules is that Ad[j]=L[k] iff ((j-1)*N)/n<k<=(j*N)/n. In the
    case k is equal to the first element of p_list, Sd[j]=j.
    NOTE: The first element of L is never considered
    As such n should be higher than N.

    EXAMPLES:
        sage: Ad=[1 for i in range(5)]
        sage: Sd=[1 for i in range(5)]
        sage: l=[3,4,5,6]
        sage: p_list=[2,3,5]
        sage: fill(Ad,Sd,3,5,l,p_list)
        sage: Ad
        [1, 1, 4, 1, 5]
        sage: Sd
        1, 1, 1, 1, 2]
    """
    k=1
    j=0
    while j<=n-1:
        if k*n<=(j*N):
            Ad[j]=L[k]
            if p_list and k==p_list[0]:
                Sd[j] = p_list.pop(0)
            k+=1
        j+=1

def compute_tree( A, Ad, i, j, end):
    r"""
    This function is used to recursively fill a multiplicative binary tree
    starting from the bottom line.
    The function returns the value of the node at floor i, number j and
    modify the tree A along the way. The tree has end+1 floor
    EXAMPLES:
        sage: A=[[1 for i in range(2^i)] for i in range(4)]
        sage: Ad=[i for i in range(1,9)]
        sage: compute_tree(A,Ad,0,0,3)==factorial(8)
        True
        sage: A
        [[40320], [24, 1680], [2, 12, 30, 56], [1, 2, 3, 4, 5, 6, 7, 8]]

    """
    if i == end:
        a = Ad[j]
    else:
        a = compute_tree(A,Ad,i+1,2*j,end)*compute_tree(A,Ad,i+1,2*j+1,end)
    A[i][j] = a
    return( a )

def fill_tree( W, i ,j, end, L1, L2 ):
    r"""
    This function is used to recursively fill a binary tree starting from
    the top floor, while respecting the following relations :
    W[0][0]=1
    W[i+1][2*j]=W[i][j]%L2[i+1][2*j]
    W[i+1][2*j+1]=(W[i][j]*L1[i+1][2*j])%L2[i+1][2*j+1]
    It does not return anything.
    """
    W[i+1][2*j]   = (W[i][j]%L2[i+1][2*j])
    W[i+1][2*j+1] = (W[i][j]*L1[i+1][2*j])%L2[i+1][2*j+1]
    if i<end-1:
        fill_tree( W, i+1, 2*j, end, L1, L2 )
        fill_tree( W, i+1, 2*j+1, end, L1, L2)

def harvey_factorial( N, L, p_list):
    r"""
    INPUT: N an integer, L a list of element of a ring of characteristic
    zero possessing a change_ring(GF(p)[[]]) method for all p prime, p_list 
    a list of prime numbers
    OUTPUT: L[0]*L[1]*...*L[p-1] mod p for all p in p_list less than N.
    
    EXAMPLES:
        sage: ZZY.<Y>=ZZ[[]]
        sage: L=[1]+[ZZY[i] for i in range(1,20)]
        sage: p_list=[2,3,5,7,11,13,17]
        sage: harvey_factorial(10,L,p_list)
        [(1, 2), (2, 3), (4, 5), (6, 7)]
    """
    d = 0
    n = 1
    while n < N:
        d += 1
        n =  n*2
    Ad = [1 for i in range(n)]
    Sd = [1 for i in range(n)]
    fill( Ad, Sd, N, n, L, p_list )
    A = [ [ 1 for j in range(2^i) ] for i in range(d+1) ]
    S = [ [ 1 for j in range(2^i) ] for i in range(d+1) ]
    _ = compute_tree( A, Ad, 0, 0, d ) 
    _ = compute_tree( S, Sd, 0, 0, d )
    W = [ [ 1 for j in range(2^i) ] for i in range(d+1) ]
    fill_tree( W, 0, 0, d, A, S )
    l = [ ]
    for i in range(n):
        if Sd[i]!=1:
            GFY.<Y>=PowerSeriesRing(GF(Sd[i]))
            l.append( ( ( L[0] * W[d][i] ).change_ring( GFY ), Sd[i] ) )
    return(l)

def adding( l , i, j, a ):
    r"""
    This function adds a coefficient a to a list representing a polynomial
    over two variables, so that a is added to the coefficient of x^i Y^j
    
    EXAMPLES:
        sage: L=[[0]]
        sage: adding(l,2,3,1)
        sage: l
        [[0],[0],[0,0,0,1]]
        sage: adding(l,2,3,1)
        sage: l
        [[0],[0],[0,0,0,2]]
        sage: adding(l,1,0,-1)
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

def reverse_iso( P, p, borne ):
    r"""
    This function computes the reverse isomorphisme of Ore polynomials
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
                adding( l, i+j, j, coeff*to_add )
            coeff = -1*coeff
    return(l)


def p_curvatures( L, N ):
    r""" 
    INPUT: L a differential operator with coefficients in ZZ[Y],
    (represented by the list of its coefficients), N an integer.
    OUTPUT: A list of the characteristic polynomials of the p-curvatures of
    L for almost all p primes less than N, the almost being decided by the
    degree of the coefficients and the constant of the leading coefficient.

    EXAMPLES:
        sage: ZZY.<Y>=ZZ[]
        sage: L=[-Y^2 + 2*Y - 4, -Y^2 - 21*Y + 3, -2*Y^2 + Y + 1, -4*Y^2 - Y - 1]
        sage: p_curvatures(L,14)
        [(x^3 + 2*x^2 + ((Y + 1)/(Y + 2))*x + (Y^2 + 1)/(Y^2 + Y + 1), 3),
         (x^3 + ((3*Y^2 + 2*Y + 3)/(Y^2 + 4*Y + 4))*x^2 + ((4*Y^2 +
         4*Y)/(Y^2 + 4*Y + 4))*x + (4*Y^2 + 2*Y + 2)/(Y^2 + 4*Y + 4),
         5),
         (x^3 + 4*x^2 + ((2*Y^2 + Y + 3)/(Y^2 + 2*Y + 2))*x + (2*Y^2 +
         4*Y)/(Y^2 + 2*Y + 2),
         7),
         (x^3 + ((6*Y^2 + 7*Y + 6)/(Y^2 + 3*Y + 3))*x^2 + ((3*Y^2 +
         4)/(Y^2 + 3*Y + 3))*x + (3*Y^2 + 9*Y + 10)/(Y^2 + 3*Y + 3),
         11),
         (x^3 + ((7*Y^2 + 5*Y + 8)/(Y^2 + 10*Y + 10))*x^2 +
         ((10*Y^2 + 12*Y + 12)/(Y^2 + 10*Y + 10))*x + (10*Y^2 +
         12)/(Y^2 + 10*Y + 10),
         13)]
    """
    L2, trans_reminder = relevant_translation( L )
    d = max( P.degree( ) for P in L2 )
    L1, denom = isomorphism( L2, d )
    ZZY.< Y > = ZZ[ ]
    m = len( L1 )
    coeff = L1[ -1 ]
    M = build_matrix( L1, m )
    M = M.change_ring( ZZY )
    primes_list = list( primes( N ) )
    while primes_list[0] <= d:
        del( primes_list[ 0 ] )
    i = 0
    length = len( primes_list )
    while i < length:
        if coeff % primes_list[ i ] == 0:
            del( primes_list[ i ] )
            length += -1
        else:
            i += 1
    N = primes_list[ -1 ] + 1
    ZQY.< Y > = PowerSeriesRing( ZZ, default_prec = d + 1 )
    matrix_list =[ M( Y+a ) + O( Y^( d+1 ) ) for a in range( N ) ]
    factorial_list = harvey_factorial( N, matrix_list, primes_list )
    factorial_list = [ (B[0]/GF(B[1])(coeff), B[1]) for B in  factorial_list]
    Xi_theta_list  = [ (GF(B[1])(coeff)*B[0].charpoly(), B[1]) for B in
            factorial_list]
    Xi_x_list = [ ( reverse_iso( P[0], P[1], d+1 ), P[1] ) for P in Xi_theta_list ]
    charpoly_list = [ ]
    leading_coeff = L[-1]
    for P in Xi_x_list:
        p=P[1]
        FpY.<Y> = GF(p)[ ]
        leading_coeff_p=FpY(leading_coeff)
        l=[]
        for i in range(len(P[0])):
            pre_trans = FpY(P[0][i])
            if trans_reminder != 0:
                pre_trans=pre_trans(Y-GF(p)(trans_reminder))
            l.append(pre_trans)
        FpYx.<x>=FpY[ ]
        l=FpYx(l[ denom : ])
        charpoly_list.append((l/leading_coeff_p,p))
    return(charpoly_list)
    
def randomize( d, m ):
    ZZY.< Y > = ZZ[ ]
    L=[ZZY.random_element(d) for i in range(m+1)]
    return(L)


