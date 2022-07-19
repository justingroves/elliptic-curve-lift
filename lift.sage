def formal_integral(f):
    #Compute the formal integral of a polynomial
    deg = f.degree()
    P = f.parent()
    p = P.characteristic()
    res = 0
    for d in range(0, deg+1):
        if ((d+1) % p != 0):
            res += list(f.coefficients(sparse=False))[d] / (d+1)*P.gen()^(d+1)
    return res
	
def IntToWitt(k, p, n):
    ZZp = Zp(p, prec=n+1, type = 'fixed-mod')
    F = GF(p)
    series = ZZp(k)
    v = []
    for _ in range(n+1):
        tmp = F(series)
        v.append(tmp)
        
        series = (series - ZZp.teichmuller(tmp))
        if series == ZZp(0):
            continue #Sage has an issue dividing 0 // p?
        else:
            series = series // p    
	
    return v

def etapols(p,n):
    PP.<x,y> = PolynomialRing(Integers(p))
    
    res = []
    for i in range(1, n+1):
        P1.<x,y> = PolynomialRing(Integers(p^(i+1)))
        res.append(x^(p^i) + y^(p^i) - (x+y)^(p^i))
    
    Q.<x,y> = QQ[]
    res[0] = PP(Q(res[0]) / p) #Coerce into an integral domain to do coefficient division
    
    for i in range(2,n+1):
        t = res[i-2]
        
        for j in range(i, n+1):
            P1 = res[j-1].parent()
            t = P1(t)^p
            res[j-1] -= p^(i-1)*t
        
        res[i-1] = PP(Q(res[i-1]) / p^i)
    
    return [x for x in res]
	
def vRemoveZeros(v=[]):
    tmp = [ x for x in v if x != 0]
    if len(tmp) != 0:
        return tmp
    elif len(tmp) == 0:
        return [0]
    else: #I'm not sure if this case is needed in SAGE
        return [ v[0].parent()(0) ]
		
def vetav(p, k, v=[], pols=[],check = False):
    v = vRemoveZeros(v) 
    lgt = len(v)
    
    if lgt == 1:
        P = v[0].parent()
        return [ P(0) for i in range(0,k) ]
    
    if pols == []:
        pols = etapols(p,k)
        
    if lgt == 2: #Note: only evaluates if the number of inputs is the same as the number of indeterminates in pols
        return [ pol(v) for pol in pols ]
    else:
        v1 = [ v[i] for i in range(0, floor(lgt / 2))] 
        v2 = [ v[i] for i in range(floor(lgt / 2), lgt)]
        
        x1 = vetav(p, k, v1, pols=pols)
        
        x2 = vetav(p, k, v2, pols=pols, check=True)
        
        x3 = vetav(p, k, [sum(x for x in v1), sum(x for x in v2)], pols=pols)
        
        res = [vRemoveZeros([x1[i], x2[i], x3[i]]) for i in range(0, k) ]
        
        for i in range(2, k+1):
            pols = [ pols[i] for i in range(0, k-i+1)]
            tmp = vetav(p, k-i+1, res[i-2], pols=pols)
            for t in range(i, k+1):
                if tmp[t-i] != 0:
                    res[t-1].append(tmp[t-i])
        return [ sum(x for x in res[i]) for i in range(0, len(res))]
		
def WittProd1(v1, v2, pols=[]):
    P = v1[0].parent()
    p = P.characteristic()
    n = len(v1) - 1
    res = [ vRemoveZeros([ v1[j]^(p^(i-j))*v2[i-j]^(p^j) for j in range(0, i+1)]) for i in range(0,n + 1)]

    if n == 1:
        return [ sum(x for x in res[i]) for i in range(0, len(res))]
    if pols == []:
        pols = etapols(p, n-1)
    if len(pols) > (n-1):
        pols = pols[0:n]
    
    for i in range(2, n+1):
        l = len(res[i-1])
        for j in range(1, l):
            temp = vetav(p, n+1-i, [res[i-1][j], sum(x for x in res[i-1][0:j])])
            for t in range(i, n+1):
                if temp[t-i] != 0:
                    res[t].append(temp[t-i])

        del pols[n-i] #Check this index if something goes wrong
    
    return [ sum(x for x in res[i]) for i in range(0, len(res))]
	
def bin_tab(n, m):
    F = Integers(m)
    res = [ [F.one()], [F.one(), F.one()]]
    for i in range(1, n):
        v = [F.one()]
        for j in range(0, i):
            v.append(res[i][j] + res[i][j+1])
        v.append(F.one())
        res.append(v)
    return res
	
def Not_Zero_Vec(v):
    for i in range(0, len(v)):
        if v[i] != 0:
            return True
        else:
            return False
			
def GT_der(f, p, i, r, n, tab, pols):
    if r == 0:
        derf = f
    else:
        derf = []
        for t in f:
            coef = t[0]
            degx = t[1]
            degy = t[2]
            
            if (degx - i >= 0) and (degy - (r-i) >= 0) and Not_Zero_Vec(coef):
                bin1 = tab[degx][i]
                bin2 = tab[degy][r-i]
                
                b12 = Integer(bin1*bin2)
                
                if (b12 % p^(n-r+1) == 1):
                    derf.append([ [coef[i] for i in range(0, n+1-r)], degx-i, degy - (r-i)])
                elif (b12 % p^(n-r+1) != 0):
                    v1 = IntToWitt(b12, p, n-r)
                    
                    derf.append([ WittProd1(v1, [ coef[i] for i in range(0, n+1-r)], pols = pols), degx-i, degy - (r-i)])
                    
        if len(derf) == 0:
            derf = [ [ [0 for s in range(0, n-r + 1)], 0, 0 ] ]
        
    return derf
	
def split_Ds(f, p, upper_bound, PR):
    res = [ PR(0) for i in range(0, upper_bound + 1)]
    N = len(PR.gens())
    for i in range(0, len(f.coefficients())):
        coef = Integer(f.coefficients()[i])
        vcoef = IntToWitt(coef, p, upper_bound)
        temp_exp = PR.one()
        
        #This odd indexing is because Magma assigns generators in the order
        #of x0, x1, x2, y0, y1, y2, while Sage does x0, y0, x1, y1, x2, y2,
        #so in order for the right generators to be picked this must be done
        for k in range(0,2):
            for j in range(0,N // 2):
                temp_exp *= PR.gen(2*j + k)^(f.exponents()[i][(N/2)*k+j]) #Keep an eye on N/2 for correct indexing

        for i in range(0, upper_bound + 1):
            res[i] += PR(vcoef[i])*temp_exp

    return res
	
def old_GT_Ds(i, r, n, p, PR):
    PR1 = PolynomialRing(Integers(p^(n+1)), 2*n+2, "alpha00")
    
    PR2.<t> = PolynomialRing(PR1)
    
    tmp = min(n, n-r+1)
    
    t1 = sum(PR2.0^(s+1)*PR1.gen(s+1)^(p^(n-(s+1))) for s in range(0, tmp))
    t2 = sum(PR2.0^(s+1)*PR1.gen(n+s+2)^(p^(n-(s+1))) for s in range(0, tmp))

    t = t1^i*t2^(r-i)
    
    t = t.coefficients(sparse=False)[r:n+1]
    
    return [ split_Ds(f, p, n-r, PR) for f in t]
	
def GT_Ds(i, r, n, p, PR):
    PR1 = PolynomialRing(Integers(p^(n+1)), 2*n+2, "alpha00")
    
    PR2.<t> = PolynomialRing(PR1)
    
    tmp = min(n, n-r+1)
    
    t1 = sum(PR2.0^(s+1)*PR1.gen(s+1)^(p^(n-(s+1))) for s in range(0, tmp))
    t2 = sum(PR2.0^(s+1)*PR1.gen(n+s+2)^(p^(n-(s+1))) for s in range(0, tmp))

    t = t1^i*t2^(r-i)
    
    #Deal with the case that the degree of t is less than n+1, so the
    #coefficients on higher powers get grabbed (though they are 0)
    if t.degree() < n+1:
        s = []
        for i in range(r, t.degree()+1):
            s.append(t.coefficients(sparse=False)[i])
        for i in range(t.degree() + 1, n+1):
            s.append(PR2(0))
    else:
        s = t.coefficients(sparse=False)[r:n+1]
    
    return [ split_Ds(f, p, n-r, PR) for f in s]
	
def Pol_Root(f, r):
    P = f.parent()
    n = len(P.gens())
    res = 0
    for i in range(0, len(f.coefficients())):
        nmon = f.coefficients()[i]
        for j in range(0,n):
            nmon *= (P.gen(j))^(f.exponents()[i][j] // r)
        res += nmon
    return res
	
def Permute_Entries(array=[]):
    permute = []
    k = len(array) // 2
    for i in range(0, len(array) // 2):
        permute.append(array[i])
        permute.append(array[k+i])
    return permute
	
def GT1(f, pols=[], tab=[], vvars=[]):
    n = len(f[0][0]) - 1
    P = f[0][0][0].parent()
    p = P.characteristic()
    
    if len(pols) == 0:
        pols = etapols(p,n)
    
    PR = PolynomialRing(P, n+1, var_array=['x','y'])
    
    maxdegx = max(t[1] for t in f)
    maxdegy = max(t[2] for t in f)
    maxdeg = max(maxdegx, maxdegy)
    
    if len(tab) == 0:
        tab = bin_tab(maxdeg, p^(n+1))
        
    res = [ [] for s in range(0, n+1) ]
    
    for r in range(0, n+1):
        for i in range(0, r+1):
            if (i <= maxdegx) and (r-i <= maxdegy):
                
                derf = GT_der(f, p, i, r, n, tab, pols)
                Ds = GT_Ds(i, r, n, p, PR)
                
                for m in range(r, n+1):
                    for j in range(r, m+1):
                        for k in range(r, j+1):
                            vt = sum( (t[0][m-j])^(p^j)*(PR.0)^(t[1]*p^m)*(PR.1)^(t[2]*p^m) for t in derf )
                            
                            v = [ PR(0) for s in range(0, 2*n+2) ]
                            for s in range(1, (m+1)):
                                v[2*s] = PR.gen(2*s)
                                v[2*s+1] = PR.gen(2*s+1)
                            
                            tmp = Ds[k-r][j-k](v)
                            tmp = Pol_Root(tmp, p^(n-m))
                            prdct = vt*tmp
                         
                            if len(vvars) != 0:
                                for ii in range(0, len(list(prdct))):
                                    new_vvars = Permute_Entries(vvars) #Get in form (x0, y0, x1, y1, ...)
                                    res[m] += [list(prdct)[ii][0]*(list(prdct)[ii][1](new_vvars))]
                            else:
                                for ii in range(0, len(list(prdct))):
                                    res[m] += [list(prdct)[ii][0]*(list(prdct)[ii][1])]

    for i in range(0, n):
        ve = vetav(p,n-i, res[i], pols=pols)
        for j in range((i+1), (n+1)):
            if ve[j-(i+1)] != 0:
                res[j].append(ve[j-(i+1)])
                
        pols = pols[0:(n-(i+1))]

    return [ sum(t for t in res[i]) for i in range(0,len(res))]
	
def lift(a0, b0, n, pols=[], minimal=False):
    # length (n+1) -- up to a_n, b_n
    # returns vectors va, vb, vF, vH
    # pols are etapols from etas.m
    # computes canonical lifting by default
    # set minimal := true to compute minimal degree liftings
    
    F = (a0.parent()).fraction_field() #Get the fraction field of our coefficients
    p = F.characteristic() #Get the characteristic of our field
    
    #Compute the etapols for faster calculation
    if len(pols) == 0: 
        pols = etapols(p,n)
        
    Pres.<x0> = PolynomialRing(F) #Create x0 for y0^2 = x0^3 + a0x0 + b0
    
    resa = [a0] #Initiate Witt vector a
    resb = [b0] #Initiate Witt vector b
    resF = [x0] #Initiate Witt vector x
    resH = [Pres.one()] #Initiate Witt vector y (all entries will be multiplied by y0)
    
    f = x0^3 + a0*x0 + b0 #f(x0)
    
    #Determine the Hasse Invariant
    ff = f^((p-1) // 2) 
    HI = F(ff.coefficients(sparse=False)[p-1]) 
    
    #The main loop, determine the Witt vectors up to the n-th coordinate
    for i in range(0, n):
        
        #Create the polynomial ring with all unknowns
        M = (3*p^(i)-1) // 2 #Number of c_i's needed from missing x0^(ip) from integrating
        Pi = PolynomialRing(F, ['x_0','y_0', 'a_n', 'b_n'] + [ 'c_%s'%i for i in range(0,M+1)] + ['Hn'])
        
        if i == 0: #If computing the 1st coordinate
            tmppf = ff
        else: #If computing the 2nd coordinate 
            tmppf = tmppf^p*ff
        
        Fi = HI^(-(p^(i+1)-1) / (p-1))*tmppf - x0^(p^(i+1)-1) #dx1/dx0 or first bit of dx2/dx0
        
        #add rest of dx2/dx0
        if i > 0: 
            Fi -= sum( resF[j]^(p^((i+1)-j)-1)*resF[j].derivative() for j in range(1, i+1) )
        
        Fi = formal_integral(Fi) #integrate dx1/dx0 or dx2/dx0
        Fi = Fi(Pi.gen(0)) #Substitute x_0 instead of x0 so all unknowns in same ring
        
        #Add missing c_i's, but set c_(p^(i)) = 0 as it is a 'good' choice
        Fi += sum( Pi.gen(4+j)*(Pi.0)^(p*j) for j in range(0,M+1) if j != p^(i) ) 
            
        #Add missing coefficients to make x_2 regular at O
        if (not minimal) and (i == 1):
            tmp = F(3/4)*resF[1]^2 #Compute (3/4)(x_1)^2
            Fi += sum( tmp.monomial_coefficient(x0^Integer(i/p + p))^p*(Pi.0)^i for i in range(((3*p^2+p)/ 2), 2*p^2-p + 1, p))
            
        va = [ Pi(x) for x in resa] + [Pi.2] #Witt vector a with unknown a_n
        vb = [ Pi(x) for x in resb] + [Pi.3] #Witt vector b with unknown b_n
        vF = [ x(Pi.0) for x in resF] + [Fi] #Witt vector x with unknown x_n
        vG = [ Pi.1*(x(Pi.0)) for x in resH ] + [Pi.1*Pi.gen(M+5)] #Witt vector y with unknown H_n
        vone = [Pi.one()] + [Pi.zero() for j in range(0, i + 1)] #Additive identity in W_n(k)
        
        #Use algorithms to compute Witt vector product quickly
        vvars = vF + vG
        GTx = GT1( [[ vone, 3, 0], [va, 1, 0], [vb, 0, 0]], pols=pols, vvars=vvars) #x^3 + ax + b
        GTy = GT1( [[ vone, 0, 2]], pols=pols, vvars=vvars) #y^2
        
        #Grab unknown coordinate of Witt vector
        RHS = GTx[i+1] 
        LHS = GTy[i+1]

        LHS = LHS.coefficient({Pi.gen(M+5):0}) #Remove coefficient of H_n (will divide by them later)

        #Convert y_0^2 into f(x_0) in LHS
        deg = LHS.degree(Pi.1)
        tmppf2 = 1
        tmpLHS = LHS.coefficient({Pi.1:0})
        for d in [ j for j in range(2, deg+1) if j % 2 == 0]:
            tmppf2 *= f(Pi.0)
            tmpLHS += LHS.coefficient({Pi.1:d})*tmppf2  
            
        RHS -= tmpLHS #Subtract part of LHS now in terms of x_0 and not y_0 to RHS

        tmppf2 = (tmppf*f)(Pi.0) #Portion of LHS to divide RHS by

        RHS *= Pi(1/2) #Divide RHS by 2
        deg1 = RHS.degree(Pi.0) #Highest degree of RHS in x_0
        deg2 = (3*(p^(i+1)+1) / 2) #Highest degree of divisor in x_0
        quo = 0

        #Perform long division until degree of the remainder is less than degree of the divisor
        while deg1 >= deg2:
            lterm = RHS.coefficient({Pi.0:deg1})*((Pi.0)^(Integer(deg1-deg2)))
            RHS -= lterm*tmppf2
            quo += lterm
            deg1 = RHS.degree(Pi.0) #Degree of remainder 
   
        #Get coefficients of the remainder (need to force them to be 0)
        vrem = []
        for jj in range(0, RHS.degree(Pi.0)+1):
            vrem += [ RHS.coefficient({Pi.0:jj})]
                
        neqts = len(vrem)

        #Rows: correspond to x_0^i, columns: coefficient on unknowns
        Mat = Matrix(F, [ [F(vrem[j].coefficient({Pi.gen(k+1):1})) for j in range(0, neqts)]
                         for k in  [ ii for ii in range(1, (2+(M+1))+1) if ii != 3+p^(i) ]])
        
        #Vector of coefficients all evaluated at 0 for all unknowns
        vec = vector(F, [ -vrem[j]([Pi(0) for k in range(1, 2 + 2 + (M+1) + 2)]) for j in range(0, neqts)])

        vsol = Mat.solve_left(vec) #Solve the corresponding system
        
        #Vector of (now) known values to substitue to get a_n, b_n, x_n, y_n
        evalvec = [x0, 0] + [vsol[j] for j in range(0, 2+p^(i))] + [0] + [vsol[j] for j in range(2+p^(i), (2+M))] + [0]
        
        resa.append(vsol[0]) #Append new a_n
        resb.append(vsol[1]) #Append new b_n
        resF.append(Fi(evalvec)) #Append x_n substituting into F_i (i.e. x_n with unknowns)
        resH.append(quo(evalvec)) #Append F_n(x_0) such that y_n = y_0*F_n(x_0)
        
    return resa, resb, resF, resH
