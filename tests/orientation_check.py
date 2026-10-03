"""Delta_m / sin^2(theta/2) for SG(m), m=1..4, with flux edges directed by
(a) vertex creation index (as src/operators/operators.py does) or
(b) geometric direction face[0]->face[1].  Run: python3 orientation_check.py"""
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
for th in (0.8,2.3):
    s2=np.sin(th/2)**2
    for orient in ('index','geometric'):
        row=[]
        for m in (1,2,3,4):
            A=H(m,th,lambda k:k%3,orient); B=H(m,th,lambda k:2,orient)
            d=(np.trace(np.linalg.matrix_power(A,4))-np.trace(np.linalg.matrix_power(B,4))).real
            row.append(round(d/s2,6))
        print(f"theta={th} {orient:9s} Delta/s^2 =",row)
print("claimed -16(3^(m-1)+1):",[-16*(3**(m-1)+1) for m in (1,2,3,4)])
print("cell-additive -32*3^(m-1):",[-32*3**(m-1) for m in (1,2,3,4)])
