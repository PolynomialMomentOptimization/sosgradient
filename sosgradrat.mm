analysis:=proc(f);
local vars, n, x1, lsdiff, w, den, kap, gcdwden, delta, lsV, h, coefh, bsh, newh, coefnewh, bsnewh, Igrad, ts, Kap, i, j, fd, newf, phi, r, xi, vi, a, qi, b, q1, denomnewh, bsf, bsV,d,homf,contnewh,Z;

with(Groebner):
with(PolynomialTools):
with(PolynomialIdeals):
read "univsos/benchsunivsos.mm":

vars:=indets(f):
bsf:=add(ilog2(abs(numer(r)))+ ilog2(abs(denom(r))+1),r in [coeffs(f, vars)]);
printf("Bitsize of f: %a \n", bsf);

n:=nops(vars):
d:=degree(f):
x1:=vars[1];
lsdiff:=[seq(diff(f,v),v in vars)];


# ========= Testing the radical zero-dimensional condition;

Igrad:= PolynomialIdeals:-PolynomialIdeal(lsdiff);
if (PolynomialIdeals:-IsZeroDimensional(Igrad) and PolynomialIdeals:-IsRadical(Igrad)) = false then lprint(f): error "The gradient ideal is NOT radical zero-dimensional"; fi;

w,den,kap:=Groebner:-RationalUnivariateRepresentation(lsdiff,x1,output=polynomials);


# ========= Re-arranging of kappa related to variables in vars;

Kap:=[];
for i from 1 to n do
        for j from 1 to n do
                if vars[i]=lhs(kap[j]) then
                        Kap:= [op(Kap),rhs(kap[j])]; fi
                        end do;
                end do;
delta:=degree(w,x1);
printf("Degree of w: %a \n", delta);

# ========= Finding newh=f(x_1,Kap[2]/den,...,Kap[n]/den

homf:=PolynomialTools:-Homogenize(f,x0); # here, den_newf=den^d;
newh:=expand(subs(x1=den*x1,x0=den,seq(vars[i]=Kap[i],i=2..n),homf));
contnewh:=content(newh,x1,'newh');
bsnewh:=BitSizePol(newh,x1);
printf("Bitsize of newh: %a \n", bsnewh);
printf("Degree of newh: %a \n", degree(newh,x1));

# ========= Finding the quotients {phi1,...,phin} of the division of f-newh/den^d by {x1-kap_1/den,...,xn-kap_n/den};
Z:=[seq(cat(z,i),i=1..n)];
phi:=[];
r:=expand(f*den^d-contnewh*newh);
for j from 2 to n do
       i:=n+2-j;               # i from n to 2
       qi:=quo(r,vars[i]-z0*Z[i],vars[i]);
       qi:=subs(z0=1/den,seq(Z[l]=Kap[l],l=i..n),qi);
       phi:=[qi,op(phi)];
       r:=subs(vars[i]=z0*Z[i],r);
       end do;
phi:=[0,op(phi)]; # because q1=0;

return  x1, den, Kap, phi, newh, contnewh;
end proc;

#=============================================================

sosgradrat:= proc(f);
local h, newh, lsV, phi, ts, sos1, sos2, newsos1, newsos2, tsana, vars, x1, sos2newh, bssos2newh, sos2h, bssos2h, sos1newh, bssos1newh,den,Kap,contnewh, sos1h, bssos1h;
read "univsos/univsos2.mm":
read "univsos/benchsunivsos.mm":

tsana:=time[real]();
x1, den, Kap, phi, newh, contnewh:=analysis(f);
tsana:=time[real]()-tsana;
printf("Analysis runs in %f secs\n", tsana);


ts:=time[real]():
sos2newh:=univsos2(newh):
ts:=time[real]()-ts:
printf("univsos2(newh) runs in %f secs\n", ts);
printf("sosgradrat(f) runs in %f secs\n", ts+tsana);
bssos2newh:=BitSizePolSeq(sos2newh,x1);
printf("Bitsize of univsos2(newh): %a \n", bssos2newh);

fd:=fopen("/home/hieu/Desktop/computation/ScheidererPhi.mm",WRITE):
fprintf(fd, "phi:=%a:\n", phi):
fclose(fd):

fd:=fopen("/home/hieu/Desktop/computation/ScheidererSOS.mm",WRITE):
fprintf(fd,"sos:=%a:\n", sos2newh):
fclose(fd):

#return x1, den, Kap, phi, sos2newh, contnewh;
end proc;

#=============================================================

nonneg:=proc(h);
local x1, m, roo, i, mark,points;
with(RootFinding):
x1:=op(indets(h));
roo:=RootFinding:-Isolate(h);
m:=nops(roo);
if (m=0 and lcoeff(h)>0) then mark:=true; fi;
if (m=0 and lcoeff(h)<0) then mark:=false; fi;
if m>0 then
        mark:=true;
	points:=[eval(h,x1=rhs(roo[1])-1)];
	for i from 1 to m-1 do
                points:=[op(points),(rhs(roo[i])+rhs(roo[i+1]))/2];
                end do;
        points:=[op(points),rhs(roo[m])+1];
        for i from 1 to nops(points) do
                if eval(h,x1=points[i])< 0 then mark:=mark and false; fi;
                end do;
fi;
return mark;
end proc;

#=============================================================

check1:= proc(f);
local h, V, delta, phi, sos, g, i, val, vars, n, tsana, lsV,Kap,A,B,numerB,denomB,d,x1,den,sos2newh,contnewh,m,newh;
with(Groebner):
vars:=indets(f);
d:=degree(f):
x1, den, Kap, phi, sos2newh, contnewh:=sosgradrat(f);
n:=nops(Kap);
m:=nops(sos2newh);
newh:=expand(contnewh*add(sos2newh[2*i-1]*sos2newh[2*i]^2,i=1..m/2));
A:=expand(f*den^d-newh);
B:=add(phi[i]*(vars[i]-Kap[i]/den),i=1..n);
numerB:=expand(numer(B));
denomB:=denom(B);
val:=evalb(numerB=expand(A*denomB));
printf("The result of checking is:", val);
return val;
end proc;

#=============================================================

check2:= proc(f);
local h, V, delta, phi, sos, g, i, val, vars, n, tsana, lsV,d,x1,den,sos2newh,contnewh,m,newh,roll,point,valf,valg,Kap;
with(Groebner):
vars:=indets(f);
d:=degree(f):
x1, den, Kap, phi, sos2newh, contnewh:=sosgradrat(f);
n:=nops(Kap);
m:=nops(sos2newh);
newh:=expand(contnewh*add(sos2newh[2*i-1]*sos2newh[2*i]^2,i=1..m/2));
g:=(newh+add(phi[i]*(vars[i]-Kap[i]/den),i=1..n))/den^d;
roll:=rand(-10..10);
point:=[seq(vars[i]=roll(),i=1..n)];
valf:=eval(f,point);
valg:=eval(g,point);
val:=evalb(valf=valg);
printf("The result of checking is:", val);
return val;
end proc;

#=============================================================

compu:= proc();
local l;
read "d6n3dense.mm":


for l from 1 to 50 do
printf("Computation for the polynomial l-th=: %a \n", l);
printf("The polynomial f_l=: %a \n", F[l]);
sosgradrat(F[l]);
end do;

end proc;





