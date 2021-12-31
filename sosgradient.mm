analysis:=proc(f);
local vars, n, x1, lsdiff, w, dw, den, kap, gcdwden, delta, lsV, h, coefh, bsh, newh, coefnewh, bsnewh, Igrad, ts, Kap, i, j, fd, newf, phi, r, xi, vi, a, qi, b, q1, denomnewh, bsf, bsV;

with(Groebner):
with(PolynomialIdeals):
read "univsos/benchsunivsos.mm":

vars:=indets(f):
n:=nops(vars):
x1:=vars[1];
lsdiff:=[seq(diff(f,v),v in vars)];
bsf:=max(op(map(ilog2, map(abs, [coeffs(f, vars)]))));
printf("Bitsize of f: %a \n", bsf);


# ========= Testing the radical zero-dimensional property;
Igrad := PolynomialIdeals:-PolynomialIdeal(lsdiff); 
if PolynomialIdeals:-IsZeroDimensional(Igrad) and PolynomialIdeals:-IsRadical(Igrad) = false then lprint(f): error "The gradient ideal is NOT radical zero-dimensional"; fi;
ts:=time();
w,den,kap:=Groebner:-RationalUnivariateRepresentation(lsdiff,t,output=polynomials);
ts:=time()-ts;
printf("Finding the parametrization in %f secs\n", ts);

# ========= Re-arranging of kappa related to vars;
Kap:=[];
for i from 1 to n do
	for j from 1 to n do
		if vars[i]=lhs(kap[j]) then
			Kap:= [op(Kap),rhs(kap[j])]; fi
			end do;
		end do;

# ========= Finding the list V={v1,...,vn}
ts:=time();
dw:=diff(w,t);
gcdwden:=gcdex(w,dw,t,'cow','coden');
delta:=degree(w,t);
printf("Degree of w: %a \n", delta);
lsV:=subs(t=x1,[t^delta-w/lcoeff(w),seq(expand(rem(coden*Kap[i],w,t)), i=2..n)]);
ts:=time()-ts;
bsV:=BitSizePolSeq(lsV,x1);
printf("Bitsize of V: %a \n", bsV);

# ========= Finding h=f(x1,v2,...,vn)
h:=expand(subs(seq(vars[i]=lsV[i],i=2..n),f));
printf("Degree of h: %a \n", degree(h,x1));
bsh:=BitSizePol(h,x1);
printf("Bitsize of h: %a \n", bsh);

#fd:=fopen("/home/hieu/Desktop/computation/h.mm",WRITE):
#fprintf(fd, "h:=%a:\n", h):
#fclose(fd):

# ========= Finding newh=f(x1,v2/dw,...,vn/dw)
dw:=subs(t=x1,dw);
Kap:=subs(t=x1,Kap);
newf:=subs(seq(vars[i]=Kap[i]/dw,i=1..n),f);
newh:=expand(numer(newf)):
bsnewh:=BitSizePol(newh,x1);
printf("Bitsize of newh: %a \n", bsnewh);

#fd:=fopen("/home/hieu/Desktop/computation/newh.mm",WRITE):
#fprintf(fd, "newh:=%a:\n", newh):
#fclose(fd):

# ========= Finding the quotients {phi1,...,phin} of the division of f by {x1^delta-v1,x2-v2,...,xn-vn};
ts:=time();
phi:=[];
r:=f-h;
for j from 2 to n do
	i:=n+2-j;	# i from n to 2
	xi:=vars[i];
	vi:=lsV[i];
	a:=r;
	qi:=0;
	while degree(a,xi)>0 do 
		b:=quo(a,xi,xi);
		qi:=qi+b;
		a:=expand(a-b*(xi-vi));
		end do;		
	phi:=[qi,op(phi)];
	r:=subs(xi=vi,r);
	end do;
r:=expand(r);
q1:=quo(r,x1^delta-lsV[1],x1); 		#note: after this step, r is zero
phi:=[q1,op(phi)];
ts:=time()-ts;
printf("Finding the quotients {phi1,...,phin} in %f secs\n", ts);

return h, newh, lsV, phi;
end proc;

#=================================================
sosgradient:= proc(f);
local h, newh, lsV, phi, ts, sos1, sos2, newsos1, newsos2, tsana, vars, x1, sos2newh, bssos2newh, sos2h, bssos2h, sos1newh, bssos1newh, sos1h, bssos1h;

read "univsos/univsos1.mm": read "univsos/univsos2.mm":
read "univsos/benchsunivsos.mm":



tsana:=time();
h,newh,lsV,phi:=analysis(f):
tsana:=time()-tsana;
printf("Analysis runs in %f secs\n", tsana);
vars:=indets(newh):
x1:=vars[1];

ts:=time():
sos2newh:=univsos2(newh):
ts:=time()-ts:
printf("Finding SOS decomp. of newh by using univsos2 in %f secs\n", ts);
printf("Finding SOS decomp. mod grad of f by using univsos2 for newh in %f secs\n", ts+tsana);
bssos2newh:=BitSizePolSeq(sos2newh,x1);
printf("Bitsize of univsos2(newh): %a \n", bssos2newh);

#ts:=time();
#sos2h:=univsos2(h):
#ts:=time()-ts;
#printf("Finding SOS decomp. of h by using univsos2 in %f secs\n", ts);
#printf("Finding SOS decomp. mod grad of f by using univsos2 in %f secs\n", ts+tsana);
#bssos2h:=BitSizePolSeq(sos2h,x1);
#printf("Bitsize of univsos2(h): %a \n", bssos2h);

#ts:=time():
#sos1newh:=univsos1(newh):
#ts:=time()-ts:
#printf("Finding SOS decomp. of newh by using univsos1 in %f secs\n", ts);
#printf("Finding SOS decomp. mod. grad. of f by using univsos1 for newh in %f secs\n", ts+tsana);
#bssos1newh:=BitSizePolSeq(sos1newh,x1);
#printf("Bitsize of univsos1(newh): %a \n", bssos1newh);

#ts:=time();
#sos1h:=univsos1(h):
#ts:=time()-ts;
#printf("Finding SOS decomp. of h by using univsos1 in %f secs\n", ts);
#printf("Finding SOS decomp. mod. grad. of f by using univsos1 in %f secs\n", ts+tsana);
#bssos1h:=BitSizePolSeq(sos1h,x1);
#printf("Bitsize of univsos1(h): %a \n", bssos1h);

return sos2newh; #sos2, newsos1, newsos2, lsV, phi;
end proc;

check:= proc(f);
local h, V, delta, phi, sos, g, i, val, vars, n, tsana, lsV;
with(Groebner);
vars:=indets(f);
sos,lsV,phi:=sosgrad(f);
n:=nops(lsV);
h:=0;
for i from 1 to nops(sos)/2 do 
		h:=h+sos[2*i-1]*(sos[2*i]^2); 
		end do;
g:=h+phi[1]*(vars[1]^delta-lsV[1]);
for i from 2 to n do
		g:=g+phi[i]*(vars[i]-lsV[i]);
		end do;
g:=expand(g);
val:=evalb(f=g);
printf("The result of checking is:", val);

end proc;

