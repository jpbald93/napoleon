import cmath,random
def nap(A,B,C,z):
    X=B+(C-B)*z; Y=C+(A-C)*z; Z=A+(B-A)*z
    Ga=(B+C+X)/3; Gb=(C+A+Y)/3; Gc=(A+B+Z)/3
    d=[abs(Ga-Gb),abs(Gb-Gc),abs(Gc-Ga)]
    return max(d)-min(d), Ga,Gb,Gc
r=lambda: complex(random.uniform(-5,5),random.uniform(-5,5))
w=cmath.exp(-1j*cmath.pi/3)
print("pos max", max(nap(r(),r(),r(),w)[0] for _ in range(1000)))
print("pos inward", max(nap(r(),r(),r(),w.conjugate())[0] for _ in range(1000)))
print("neg control (rot 50deg)", min(nap(r(),r(),r(),cmath.exp(-1j*(50*cmath.pi/180)))[0] for _ in range(1000)))
print("neg control (mixed orientation)", end=" ")
A,B,C=r(),r(),r(); X=B+(C-B)*w; Y=C+(A-C)*w.conjugate(); Z=A+(B-A)*w
Ga=(B+C+X)/3; Gb=(C+A+Y)/3; Gc=(A+B+Z)/3; print(abs(Ga-Gb)-abs(Gb-Gc))
_,Ga,Gb,Gc=nap(A,B,C,w); print("ratio (Gb-Ga)/(Gc-Ga)=",(Gb-Ga)/(Gc-Ga), "w=",w)
