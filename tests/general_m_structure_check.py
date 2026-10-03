"""Structure behind Delta_m for SG(m) (all numbers are numerical checks, not proofs).

 1. Delta = Tr(A^4) - Tr(A'^4): the degree part D of H = D - A drops out.
 2. Delta equals the sum over ordered vertex pairs (v,w), v != w, with exactly two common
    neighbours (rhombus diagonals) of ||(A^2)_vw||_F^2 - ||(A'^2)_vw||_F^2.
 3. With flux edges directed by vertex index, the number of faces whose flux edge is directed
    against +x is F_m = (3^(m-1)-1)/2 (all with face index = 1 mod 3), and
        Delta_m / sin^2(theta/2) = -32 * (3^(m-1) - F_m) = -16 * (3^(m-1) + 1).
"""
import numpy as np
def build(level):
    V=[(0.0,0.0),(1.0,0.0),(0.0,1.0)]; E=[(0,1),(1,2),(0,2)]; faces=None
    for _ in range(level):
        offs=[(0.0,0.0),(0.5,0.0),(0.0,0.5)]; nV=[]; vi={}; nE=set(); maps=[]
        for ox,oy in offs:
            m={}
            for i,(x,y) in enumerate(V):
                p=(round(x*.5+ox,10),round(y*.5+oy,10))
                if p not in vi: vi[p]=len(nV); nV.append(p)
                m[i]=vi[p]
            maps.append(m)
        nF=[]
        for m in maps:
            for a,b in E: nE.add(tuple(sorted((m[a],m[b]))))
            if faces is not None:
                for f in faces: nF.append(tuple(m[v] for v in f))
            else: nF.append((m[0],m[1],m[2]))
        V,E,faces=nV,list(nE),nF
    return V,E,faces
S=[np.array([[0,1],[1,0]],complex),np.array([[0,-1j],[1j,0]]),np.array([[1,0],[0,-1]],complex)]
rot=lambda a,t:np.cos(t/2)*np.eye(2)-1j*np.sin(t/2)*S[a]
def H(level,th,axis_fn,orient):
    V,E,F=build(level); n=len(V)
    M=np.zeros((2*n,2*n),complex); deg=[0]*n
    for i,j in E: deg[i]+=1;deg[j]+=1
    for i in range(n): M[2*i:2*i+2,2*i:2*i+2]=deg[i]*np.eye(2)
    fl=set()
    for k,f in enumerate(F):
        a,b=(sorted((f[0],f[1])) if orient=='index' else (f[0],f[1]))
        fl.add(frozenset((a,b)))
        U=rot(axis_fn(k),th)
        M[2*a:2*a+2,2*b:2*b+2]=-U; M[2*b:2*b+2,2*a:2*a+2]=-U.conj().T
    for i,j in E:
        if frozenset((i,j)) not in fl:
            M[2*i:2*i+2,2*j:2*j+2]=-np.eye(2); M[2*j:2*j+2,2*i:2*i+2]=-np.eye(2)
    return M

def structure(m, th, orient):
    V, E, _ = build(m); n = len(V)
    M  = H(m, th, lambda k: k % 3, orient); Mp = H(m, th, lambda k: 2, orient)
    deg = [0]*n
    for i, j in E: deg[i] += 1; deg[j] += 1
    D = np.zeros_like(M)
    for i in range(n): D[2*i:2*i+2, 2*i:2*i+2] = deg[i]*np.eye(2)
    A, Ap = D - M, D - Mp
    P4 = lambda X: np.trace(np.linalg.matrix_power(X, 4)).real
    nb = [set() for _ in range(n)]
    for i, j in E: nb[i].add(j); nb[j].add(i)
    A2, Ap2 = A @ A, Ap @ Ap
    pairs = sum(np.linalg.norm(A2[2*v:2*v+2, 2*w:2*w+2])**2 - np.linalg.norm(Ap2[2*v:2*v+2, 2*w:2*w+2])**2
                for v in range(n) for w in range(n) if v != w and len(nb[v] & nb[w]) == 2)
    mx = max(len(nb[v] & nb[w]) for v in range(n) for w in range(n) if v != w)
    return P4(M) - P4(Mp), P4(A) - P4(Ap), pairs, mx

if __name__ == "__main__":
    th = 1.3; s2 = np.sin(th/2)**2
    for orient in ("geometric", "index"):
        for m in (1, 2, 3):
            f, a, p, mx = structure(m, th, orient)
            print(f"{orient:9s} m={m}: Delta/s2={f/s2:9.3f}  TrA4-TrA'4 /s2={a/s2:9.3f}  rhombus-pairs/s2={p/s2:9.3f}  max common nbrs={mx}")
    for m in range(1, 8):
        _, _, F = build(m)
        fl = [k for k, f in enumerate(F) if f[0] > f[1]]
        print(f"m={m}: faces={len(F)} flipped={len(fl)} (3^(m-1)-1)/2={(3**(m-1)-1)//2} face index mod 3 in {sorted(set(k % 3 for k in fl))}")
