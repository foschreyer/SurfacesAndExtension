///
restart
loadPackage( "SurfacesAndExtensions",Reload=>true)

 
uninstallPackage("SurfacesAndExtensions")

restart
installPackage("SurfacesAndExtensions")
viewHelp SurfacesAndExtensions

check ("SurfacesAndExtensions")

peek loadedFiles
///

newPackage(
	"SurfacesAndExtensions",
    	Version => "0.5", 
    	Date => "October 4, 2023",
    	Authors => { 
	         {Name => "Frank-Olaf Schreyer", 
		  Email => "schreyer@math.uni-sb.de", 
		  HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
                   {Name => "Hoang Le Truong", 
		  Email => "hltruong@math.ac.vn", 
		  HomePage => ""}
	         },
    	Headline => "rational surface and extensions",
    	DebuggingMode => true
    	)

export {
    "linearSystemOnRationalSurface",
    "expectedDimension",
    "rationalSurface",
    "adjointMatrix",
    "slowAdjunctionCalculation",
    "adjunctionProcess",
    "parametrization",
    "extension",
    "threeRegularSurfaceOfCodim3",
    "maximalExtensionOfReyeFanoModel",
    "reyeCongruence",
    "tangentCone1",
    "fanoPolarizedEnriquesSurface",
    "listOfN33Surfaces",
    "extensionsOfAGeneralParacanonicalCurve",
    "extensionsOfAGeneralPrymCanonicalCurve",
    "extensionsOfNodalPrymCurve",   
    "prymCanonicalEmbeddedPlaneQuintic",
    "paracanonicalEmbeddedPlaneQuintic",
    "analyseFanoPolarizedEnriquesSurface",
    "specialFamiliesOfSommeseVandeVen",
    "identifyMaximalExtension",
    "extensionsOfSpecialCurves"
    }
    




linearSystemOnRationalSurface=method()
linearSystemOnRationalSurface(Ring,ZZ,List) := (P2,d,L) -> (
    -- P2, the ring of P2
    -- d, a degree
    -- L, the multiplicities of the assigned base points
    pts:=apply(#L,i->ideal random(P2^1,P2^{2:-1}));
    assert(degree intersect pts == #L);
    I:=intersect apply(#L,i->(pts_i)^(L_i));
    Id:=gens intersect(I, ideal basis(d,P2));
    pos:=positions(toList(0..rank source Id-1),i->degree ideal Id_(0,i)==d);
    Id_pos)

linearSystemOnRationalSurface(List,ZZ,List) := (points,d,L) -> (
    -- P2, the ring of P2
    -- d, a degree
    -- L, the multiplicities of the assigned base points
    P2 := ring points_0;
    assert(degree intersect points == #L);
    I:=intersect apply(#L,i->(points_i)^(L_i));
    Id:=gens intersect(I, ideal basis(d,P2));
    pos:=positions(toList(0..rank source Id-1),i->degree ideal Id_(0,i)==d);
    Id_pos)



expectedDimension=method()
expectedDimension(ZZ,List) := (d,L) -> (
    -- d, a degree
    -- L, the multiplicities of the assigned base points
    max(0,binomial(d+2,2)-sum(L,r->binomial(r+1,2))))

rationalSurface=method()
rationalSurface(Ring,ZZ,List,Symbol) := (P2,d,L,x) -> (
    -- P2, the ring of P2
    -- d, a degree
    -- L, the multiplicities of the assigned base points
    -- x, a symbol for the new variable names
    n:= expectedDimension(d,L)-1;
    Pn := coefficientRing P2[x_0..x_n];
    H := linearSystemOnRationalSurface(P2,d,L);
    phi:= map(P2,Pn,H);
    trim  ker phi
    )

rationalSurface(Ring,ZZ,List,Ring) := (P2,d,L,Pn) -> (
    -- P2, the ring of P2
    -- d, a degree
    -- L, the multiplicities of the assigned base points
    -- Pn, coordinate ring of Pn
    H := linearSystemOnRationalSurface(P2,d,L);
    assert( rank source H == dim Pn);
    phi:= map(P2,Pn,H);
    trim  ker phi)

rationalSurface(List,ZZ,List,Symbol) := (points,d,L,x) -> (
    -- points, a List of points in P2, 
    -- d, a degree
    -- L, the multiplicities of the assigned base points
    -- x, a symbol for the new variable names
 -- n:= expectedDimension(d,L)-1;
    H := linearSystemOnRationalSurface(points,d,L);
    P2 := ring H;
    n := rank source H-1;
    Pn := (coefficientRing P2)[x_0..x_n];
    phi:= map(P2,Pn,H);
    trim  ker phi
    )



adjointMatrix=method()
adjointMatrix(Matrix,Symbol) := (D,z) -> (
    --  Input: D, matrix, transposed presentation matrix of omega_X
    --            where X is the surface defiend by ann coker D
    --         z, symbol
    --  Output: adj, matrix, presentation matrix of O_X(H) 
    --               as a module over the adjoint surface, X', i.e.,
    --               the image of X under |K+H|             
    R := ring D;
    kk := coefficientRing R;
    r := rank source D; 
    P := kk[z_0..z_(r-1)];
    -- assert that D is a linear matrix
    tal1:=tally degrees source D;
    tal2:=tally degrees target D;
    degs1:=flatten keys tal1;
    degs2:=flatten keys tal2;
    assert(#degs1==1 and #degs2 ==1);
    assert(degs1_0==degs2_0+1);
    RxP := R**P;
    --tripel tensor flip
    adj := map(P^(numgens R),,sub(transpose diff( sub(vars R,RxP),sub(D,RxP)*sub(transpose vars P,RxP)),P));
    adj)

slowAdjunctionCalculation=method()
slowAdjunctionCalculation(Ideal,Matrix,Symbol):= (I,D,y) -> (
    n:=rank source D-1;
    P:= ring I;
    kk:= coefficientRing P;
    Pn:=kk[y_0..y_n];
    PxPn:= P**Pn;
    graph:= ideal( (sub(D,PxPn)*sub(transpose vars Pn,PxPn)))+sub(I,PxPn);
    gs:= gens saturate(graph,ideal PxPn_0);
    tally degrees source gs;
    -- we assume that I is non-degenerate, more precisely, V(I) is not contained in V(P_0);
    pos0:= positions(degrees source gs,de-> de_0==0);
    I1:=ideal sub(gs_pos0,Pn);
    pos1:= positions( degrees source gs,de-> de_0==1);
    adj:=sub(diff(transpose sub(vars P,PxPn),(gs_pos1)),Pn);
    adj=map(Pn^(rank target adj),,adj);
    (I1,adj)
    )


    
   
    
    



adjunctionProcess=method()
adjunctionProcess(Ideal):= J -> (
    --  Input: I, ideal of a surface
    --  Output:
    --       numList, list of numerical data ()
    --       adjList, list of adjunction matrices, 
    --                (useful for the computation of a rational parametrization)
    --       ptsList, list of the ideals of exceptional pts
    --       I, ideal of the last adjoint surface
    I:=J;
    numList:={}, rd:=null; adjList:={};ptsList:={};
    a:=symbol a; b:=symbol b;
    ab:={symbol a,symbol b};
    Pn:=ring J;n:= dim Pn-1; deg := degree I; sectGenus:=genus(I+ideal(Pn_0));
    betti(fI:=res(I,FastNonminimal=>true));
    c:=codim I;
	betti (G:=((dual fI[-c])**Pn^{-n-1}));
	betti(omega:=prune HH_0 G);
        betti(D:=transpose presentation omega);
	numList=append(numList,(n,deg,sectGenus));
    y:= null; adj:=null; pts:=null; l:=null;
    tal1:=null;tal2:=null,degs1:=null;degs2:=null;I1:=null;
    while ( rank source D >2 ) 
    	do ( 
	    y=first ab;ab=reverse ab;
	    tal1=tally degrees source D;
    	    tal2=tally degrees target D;
    	    degs1=flatten keys tal1;
    	    degs2=flatten keys tal2;
    	    if (#degs1==1 and #degs2 ==1 and degs1_0==degs2_0+1) then (
		betti(adj=adjointMatrix(D,y));
		I1=ann coker adj) else return (numList,adjList,ptsList,I);
	    while (
		rd=random((ring adj)^3,target adj);
		not dim (ideal (sub(rd,Pn)*transpose vars Pn)+I)==0) do ();
	    --pts=saturate ann coker(transpose (syz rd)*adj);
	    pts=sum apply(3,i->saturate ann coker(transpose syz(rd^{i})*adj));
	    ptsList=append(ptsList,pts);
	    l=if dim pts ==1 then degree pts else 0;
	    numList=append(numList,l);
	    adjList=append(adjList, adj);
	    I=I1;
	    c =codim I;
    	    Pn=ring I;
	    n=dim Pn-1;
	    deg=degree I; 
	    sectGenus=genus(I+ideal (Pn_0));
	    betti(fI=res(I,FastNonminimal=>true));
	    betti (G=((dual fI[-c])**Pn^{-n-1}));
	    betti(omega=prune HH_0 G);
            betti(D=transpose presentation omega);
	    numList=append(numList,(n,deg,sectGenus));
	    );
	(numList,adjList,ptsList,I))


adjunctionProcess(Ideal,ZZ):= (J,k) -> (
    --  Input: I, ideal of a surface
    --         k, number of adjunction steps 
    --  Output:
    --       numList, list of numerical data ()
    --       adjList, list of adjunction matrices, 
    --                (useful for the computation of a rational parametrization)
    --       ptsList, list of the ideals of exceptional points
    --       I, ideal of the last adjoint surface
    I:=J;
    numList:={}, rd:=null; adjList:={};ptsList:={};
    a:=symbol a; b:=symbol b;
    N:=0;
    ab:={symbol a,symbol b};
    Pn:=ring J;n:= dim Pn-1; deg := degree I; sectGenus:=genus(I+ideal(Pn_0));
    betti(fI:=res(I,FastNonminimal=>true));
    c:= codim I;
	betti (G:=((dual fI[-c])**Pn^{-n-1}));
	betti(omega:=prune HH_0 G);
        betti(D:=transpose presentation omega);
	numList=append(numList,(n,deg,sectGenus));
    y:= null; adj:=null; pts:=null; l:=null;
    tal1:=null;tal2:=null,degs1:=null;degs2:=null;I1:=null;
    while (
	rank source D >2 and N<k
	) 
    	do ( N=N+1;
	    y=first ab;ab=reverse ab;
	    tal1=tally degrees source D;
    	    tal2=tally degrees target D;
    	    degs1=flatten keys tal1;
    	    degs2=flatten keys tal2;
    	    if (#degs1==1 and #degs2 ==1 and degs1_0==degs2_0+1) then (
		betti(adj=adjointMatrix(D,y));
		I1=ann coker adj) else return (numList,adjList,ptsList,I);
	    while (
		rd=random((ring adj)^3,target adj);
		not dim (ideal (sub(rd,Pn)*transpose vars Pn)+I)==0) do ();
	    --pts=saturate ann coker(transpose (syz rd)*adj);
	    pts=sum apply(3,i->saturate ann coker(transpose syz(rd^{i})*adj));
	    ptsList=append(ptsList,pts);
	    l=if dim pts ==1 then degree pts else 0;
	    numList=append(numList,l);
	    adjList=append(adjList, adj);
    	    I=I1;
	    c =codim I;
    	    Pn=ring I;
	    n=dim Pn-1;
	    deg=degree I; 
  	    sectGenus=genus(I+ideal (Pn_0));
  	    betti(fI=res(I,FastNonminimal=>true));
	    betti (G=((dual fI[-c])**Pn^{-n-1}));
	    betti(omega=prune HH_0 G);
            betti(D=transpose presentation omega);
	    numList=append(numList,(n,deg,sectGenus));
	    );
	(numList,adjList,ptsList,I))




parametrization=method()
parametrization(Ring,List) := (P2,adjList) -> (
    n:=#adjList;
    H:=vars P2;
    Ht:= null;
    while n>0 do (
	betti(Ht= syz transpose map(P2^(rank target adjList_(n-1)), , sub(adjList_(n-1),H)));
	H=map(P2^1,,transpose (Ht_{0}));
	n=n-1);
   H)



extension=method()
extension(Ideal,ZZ) := (J,k) -> (
    betti(fJ:=res(J,LengthLimit=>k+1));
    k1:=keys tally degrees fJ_(k-1);
    k2:=keys tally degrees fJ_k; 
    k3:=keys tally degrees fJ_(k+1);  
    if not(#k1==1 and #k2==1 and #k3==1 and k1_0_0+1==k2_0_0 and k2_0_0+1==k3_0_0) 
       then error "expected linear matrices in the resolution";
    R:= ring J;
    kk:= coefficientRing R;
    n1:= rank fJ_(k-1);
    n2:= rank fJ_k;
    n3:= rank fJ_(k+1);
    a := symbol a; b:=symbol b;
    ab:=kk[a_(0,0)..a_(n1-1,n2-1),b_(0,0)..b_(n2-1,n3-1)];
    A:=transpose genericMatrix(ab,a_(0,0),n2,n1);
    B:=transpose genericMatrix(ab,b_(0,0),n3,n2);    
    Rab:=R**ab;
    C := sub(fJ.dd_k,Rab)*sub(B,Rab) + sub(A,Rab)*sub(fJ.dd_(k+1),Rab);
    linRel:=sub(diff(sub(vars R,Rab),flatten C),ab);    
    subLin :=vars ab%trim ideal linRel;
    S:=kk[support subLin];
    A1:=sub(sub(A,subLin),S);
    B1:=sub(sub(B,subLin),S);
    eq:=trim ideal (A1*B1);        
    (A1,B1,eq))

threeRegularSurfaceOfCodim3=method()
threeRegularSurfaceOfCodim3(ZZ,Ring) := (kSquare,kk) -> (
    t := symbol t; x:= symbol x;
    P2:=kk[t_0..t_2];P5:=kk[x_0..x_5];
    I:= if kSquare == -6 then rationalSurface(P2,5,toList(15:1),P5) else
        if kSquare == -5 then rationalSurface(P2,6,toList(4:2)|toList(10:1),P5) else
	if kSquare == -4 then rationalSurface(P2,7,toList(1:3)|toList(6:2)|toList(6:1),P5) else
	if kSquare == -3 then rationalSurface(P2,7,toList(9:2)|toList(3:1),P5) else
        if kSquare == -2 then rationalSurface(P2,9,toList(6:3)|toList(4:2)|toList(1:1),P5) else
        if kSquare == -1 then rationalSurface(P2,10,toList(10:3),P5) else
	if kSquare == 0 then  ((J,p):=fanoPolarizedEnriquesSurface(kk,symbol x);J);
    I)

maximalExtensionOfReyeFanoModel=method()
maximalExtensionOfReyeFanoModel(Ring,Symbol) := (kk,z) -> (
    x := symbol x;
    P5:=kk[x_0..x_5];
    m:=genericSkewMatrix(P5,x_0,4);
    betti(M:=directSum apply(4,i->m));
    q:=pfaffians(4,m);
    N:=map(P5^16,,M*syz matrix{{1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1}});
    Sq:=P5/q;
    betti(fN:=res(coker (N**Sq),LengthLimit=>6));
    assert(dim minors(2,sub(fN.dd_3,P5))==0 and rank fN.dd_3 == 3 );
    D1:=sub(fN.dd_2,P5);
    betti(D:=adjointMatrix(D1,z));
    ann coker D
    )

reyeCongruence=method()
reyeCongruence(Ideal,Ring) := (I,P5) -> (
    --if not (coefficientRing ring I=== coefficientRing P5) then error "expected the same coefficient ring";
    if not (dim ring I==4 and degrees source gens I==toList(4:{2})) then error "expected an ideal generated by four quadrics in P3";
    if not dim P5==6 then error "expected the homogeneous coordinate ring of a P5";    
    kk:= coefficientRing P5;
    a := symbol a; 
    stiefelCoord:=kk[a_0..a_7];
    A:=transpose genericMatrix(stiefelCoord,a_0,4,2);
    betti(J:=minors(3,sub(gens I,A^{0})||sub(gens I,A^{1})||sub(gens I,A^{0}+A^{1})));
    pluckerCoord := gens minors(2,A);
    phi:= map(stiefelCoord,P5,pluckerCoord);
    q := ker phi;
    rel:=sub(syz(symmetricPower(3,pluckerCoord)%J,DegreeLimit=>6),kk);
    IReye:=trim (q+ideal(symmetricPower(3,vars P5)*rel));
    IReye)

tangentCone1=method()
tangentCone1(Matrix,Ideal) := (pt,X) -> (
--tangentCone(Matrix,Ideal) := (pt,X) -> (
    spt:=syz pt;
    mCoordinateChange:=pt||transpose spt;
    assert( not det mCoordinateChange==0);
    P:=ring X;
    coordinateChange:=map(P,P,vars P*mCoordinateChange);
    X':=coordinateChange X;
    Xaff:=sub(X',{P_0=>1});
    kk:=coefficientRing P;
    P1:=kk[support Xaff];
    Xaff=sub(Xaff,P1);
--    tangentCone Xaff
    Xaff
    )

fanoPolarizedEnriquesSurface=method()
fanoPolarizedEnriquesSurface(Ring,Symbol) :=(kk,z) -> (
    x := symbol x;
    P4:=kk[x_0..x_4];
    C:=ideal random(P4^1,P4^{3:-2});
    b:=basis(2,P4);
    m:=b*syz transpose diff(transpose b,gens C);
    fm:=res ideal m;   
    I:= trim ideal( fm.dd_4*syz fm.dd_4^{15..20});
    (numList,adjList,ptsList,I1) := adjunctionProcess(I,1);
    P5:=kk[z_0..z_5];
    J:=sub(I1,vars P5);
    pt :=sub(ptsList_0,vars P5);
    pt=saturate pt;
    assert(pt==pt+J);
    return (J,pt))

listOfN33Surfaces=method()
listOfN33Surfaces(Ring) := kk -> (
    Y:=null;A:=null;B:=null;eq:=null;
    apply(toList(-6..0),k2-> (
	    Y= threeRegularSurfaceOfCodim3(k2,kk);
	    (k2,Y)))
    )
	    
extensionsOfAGeneralParacanonicalCurve=method()
extensionsOfAGeneralParacanonicalCurve(String) := S -> (
    setRandomSeed(S);
    print "
    kk=ZZ/nextPrime(10^3)
    P2=kk[x_0..x_2]
    L=toList(4:2)|toList(10:1)
    Y=rationalSurface(P2,6,L,symbol y);
    minimalBetti Y
    dim Y
    C=ideal(gens Y %ideal random(1,ring Y));
    P4=kk[support C]
    C=sub(C,P4);
    (A,B,eq) = extension(C,2);
    betti eq
    dim ring A, codim eq, degree eq
    elapsedTime betti(feq=res( eq,FastNonminimal=>true)) -- 2.30677 seconds elapsed
    elapsedTime betti(I5=ann coker transpose  feq.dd_9) -- 11.1692 seconds elapsed
    dim I5, degree I5
    betti(fI5=res( I5,FastNonminimal=>true))
    betti (D=fI5.dd_9^{7..87})
    betti(D1=adjointMatrix(D,symbol z))
    betti(fD1=res(coker D1,FastNonminimal=>true))
    betti(ID1=ann coker transpose fD1.dd_9)
    dim ID1, degree ID1
    minimalBetti ID1
    elapsedTime cID1=decompose ID1;
    tally apply(cID1,c->(dim c, degree c, betti c))
    -- not all of the 20 components are defined over the finite ground kk
    -- we could pass to a finite Galois field to get them seperated
    e= lcm apply(cID1,c->degree c)
    -- kke=GF(char kk,e)
    -- we avoid this beause our ground field is akready not so small.    
    I5a=apply(select(cID1,c-> degree c ==1),c->trim ideal (D*sub(syz transpose jacobian c,kk)));
    Y5s=apply(I5a,c->(Y5=ideal syz (transpose A%c);P5=kk[support Y5];sub(Y5,P5)));
    tally apply(Y5s,c->(dim ring c,minimalBetti c))
    
    elapsedTime betti(rest=eq:I5) -- 14.6976 seconds elapsed
    elapsedTime betti( frest=res rest )  -- 3.48289 seconds elapsed      
    elapsedTime betti(I7=ann coker transpose frest.dd_7) -- 4.55569 seconds elapsed       
    dim I7, degree I7
    betti(I9=rest:I7)
    betti(Z9=(ideal syz (transpose A%I9)))
    P9=kk[support Z9], dim P9==10, Z9=sub(Z9,P9);
    Y9=ideal (gens sub(Z9,P9)%ideal random(P9^1,P9^{4:-1}));
    P5=kk[support Y9]
    dim P5==6
    Y9=sub(Y9,P5);
    betti(fadj=res coker  adjointMatrix(frest.dd_7,symbol z))
    betti (J7=ann coker transpose fadj.dd_4)
    cJ7=decompose J7
    cI7=apply(cJ7,c-> trim ideal(frest.dd_7*sub(syz transpose jacobian c,kk)));
    Z7s=apply(cI7,c->(Z7=ideal syz transpose (A%c);P7=kk[support Z7]; Z7=sub(Z7,P7)));
    tally apply(Z7s,c->(dim ring c,minimalBetti c))
    
    Y7s=apply(Z7s,Z->(
	    P7=ring Z;
	    Y=trim ideal( gens Z%ideal random(P7^1,P7^{2:-1}));
	    P5=kk[support Y]; 
	    sub(Y,P5)));
    Ys={Y9}|Y7s|Y5s;
    tally apply(Ys,Y->minimalBetti Y)
    tally apply(Ys,Y->((numList,adjList,ptsList,I)=adjunctionProcess(Y,1); 
              (numList, minimalBetti I)))    
    "
)


extensionsOfAGeneralPrymCanonicalCurve=method()
extensionsOfAGeneralPrymCanonicalCurve(String) := S -> (
    setRandomSeed(S);
    print "
    kk=ZZ/nextPrime 10^3
    (E,pt)=fanoPolarizedEnriquesSurface(kk,symbol y);
    betti E
    P5= ring E
    C=ideal(gens E%ideal random(P5^1,P5^{1:-1}));
    P4=kk[support C], dim P4==5
    C=sub(C,P4);
    (A,B,eq)=extension(C,2);
    betti eq
    dim ring eq
    elapsedTime dim eq, degree eq -- 13.6068 seconds elapsed
    elapsedTime betti(feq=res(eq,FastNonminimal=>true)) -- 20.2925 seconds elapsed
    elapsedTime betti(I5=ann coker transpose feq.dd_9) -- 11.6754 seconds elapsed
    dim I5, degree I5
    minimalBetti I5
    betti(fI5=res(I5,FastNonminimal=>true))
    betti(D1=adjointMatrix(fI5.dd_9^{6..95},symbol t))
    betti(fD1=res(coker D1,FastNonminimal=>true))
    betti(J1=ann coker transpose fD1.dd_10)
    dim J1, degree J1, dim ring J1
    elapsedTime cJ1=decompose J1;#cJ1
    tally apply(cJ1,c->degree c)
    cJ11=select(cJ1,c->degree c== 1)
    Ls=apply(cJ11,c->trim ideal(fI5.dd_9*sub(syz transpose jacobian c,kk)));
    apply(Ls,L->dim L)
    Y5s=apply(Ls,c->(Z=ideal syz transpose (A%c);P5=kk[support Z];sub(Z,P5)));

    elapsedTime betti(rest=eq:I5)  -- 22.7577 seconds elapsed
    elapsedTime betti( frest=res rest )  -- 3.48289 seconds elapsed      
    elapsedTime betti(I7=ann coker transpose frest.dd_7) -- 4.55569 seconds elapsed       
    dim I7, degree I7
    betti(fadj=res coker  adjointMatrix(frest.dd_7,symbol z))
    betti (J7=ann coker transpose fadj.dd_4)
    cJ7=decompose J7
    tally apply(cJ7,c->(dim c, degree c))
   
    betti(I9=rest:I7)
    betti(Z9=(ideal syz (transpose A%I9)))
    P9=kk[support Z9], dim P9==10, Z9=sub(Z9,P9);
    Y9=ideal (gens Z9%ideal random(P9^1,P9^{4:-1}));
    P5=kk[support Y9], Y9=sub(Y9,P5);
    dim P5==6
    cJ71=select(cJ7,c->degree c ==1)
    cI7=apply(cJ71,c-> trim ideal(frest.dd_7*sub(syz transpose jacobian c,kk)));
    Z7s=apply(cI7,c->(Z7=ideal syz transpose (A%c);P7=kk[support Z7]; Z7=sub(Z7,P7)));
    tally apply(Z7s,c->(dim ring c,minimalBetti c))
    Y7s=apply(Z7s,Z->(P7=ring Z;L=ideal random(P7^1,P7^{2:-1});
		Y=ideal (gens Z%L);P5=kk[support Y];sub(Y,P5)));
    Ys={Y9}|Y7s|Y5s;
    netList apply(Ys,Y->((numList,adjList,ptsList,I)=adjunctionProcess(Y,1);
	    (numList, minimalBetti I)))
    "
    )
///
S="good decompositions"
///

extensionsOfNodalPrymCurve=method()
extensionsOfNodalPrymCurve(String) := S -> (
    setRandomSeed(S);
    print "
    kk=ZZ/nextPrime 10^3
    Z=maximalExtensionOfReyeFanoModel(kk,symbol z);
    P9= ring Z
    C=ideal(gens Z%ideal random(P9^1,P9^{5:-1}));
    P4=kk[support C], dim P4==5
    C=sub(C,P4);
    (A,B,eq)=extension(C,2);
    betti eq
    dim ring eq
    elapsedTime dim eq, degree eq 
    elapsedTime betti(feq=res(eq,FastNonminimal=>true)) 
    elapsedTime betti(I8=ann coker transpose feq.dd_8)
    dim I8, degree I8
    elapsedTime cI8=decompose I8;
    tally apply(cI8,c->(dim c, degree c))
    Z5s=apply(select(cI8,c->degree c ==1),c->(Y=ideal syz transpose (A%c);
	    P5=kk[support Y];sub(Y,P5)));
    apply(Z5s,Z->dim ring Z)
    betti(rest=eq:I8)
    rest==eq
    -- => I8 is not part of the primary decomposition of eq
    tally apply(Z5s,Y->((numList,adjList,ptsList,I)=adjunctionProcess(Y,2);
	    (numList, minimalBetti I)))
    Z5=first Z5s;
    betti(singZ5=radical saturate trim (Z5+minors(2,jacobian Z5)))
    dim singZ5, degree singZ5
    -- Z5 is a Coble surface with 4 singular points
    elapsedTime betti(cycles=syz transpose feq.dd_8)
    betti(ext7=prune subquotient(cycles,transpose feq.dd_7))
    betti(I7=ann ext7)
    dim I7, degree I7, codim I7
    betti(fI7=res(I7,FastNonminimal=>true))
    betti (cycles1=syz transpose fI7.dd_8)
    betti(ext7=prune subquotient(cycles1,transpose fI7.dd_7))

    betti(adj1=adjointMatrix(transpose presentation ext7,symbol x))
    betti(fadj1=res(coker adj1, FastNonminimal=>true))    
    betti(fivePts=ann coker transpose fadj1.dd_4)
    dim fivePts, degree fivePts
    cfivePts=decompose fivePts
    tally apply(cfivePts,c->degree c)
    pts=apply(select(cfivePts,c->degree c==1),c->sub(syz transpose jacobian c,kk))
    Ls=apply(pts,p-> trim ideal(transpose p*presentation ext7));
    Z7s=apply(Ls,L->(Z=ideal syz transpose (A%L);P7=kk[support Z];sub(Z,P7)));
    betti(I9=eq:I7)
    minimalBetti I9
    intersect(I7,I9)==eq 
    I9s=decompose I9;
    intersect(I9s)==I9
    -- => got correct primary decomposition, the ideal is radical with components 
    --   those of I9 and I7
    apply(I9s,I->I+I8==I8)
    Z9s=apply(I9s,c->(Z=ideal syz transpose (A%c);P9=kk[support Z];sub(Z,P9)));
    Zs=Z9s|Z7s|Z5s;  
    tally apply(Zs,Z->(dim ring Z, #support Z))
    Ys=apply(Zs,Z->(P=ring Z;Y=ideal(gens Z%ideal random(P^1,P^{dim P-6:-1}));
		P5=kk[support Y];sub(Y,P5)));
    tally apply(Ys,Y-> dim ring Y)
    (numlist,sdjList,ptsList,I)=adjunctionProcess( first Ys,1);
    numlist,minimalBetti I
    -- => the components of I8 are contained in the component corresponding to
    --    to the nodal Enriques surface 
    tally apply(Ys,Y->((numList,adjList,ptsList,I)=adjunctionProcess(Y,1);
	    (numList, minimalBetti I)))
    betti (intIs9=trim sum I9s)
    betti(X=trim ideal syz transpose (A% intIs9)) 
    #support X ==5 
    -- => the two 4-dimensional families do not intersect
    betti first cI8, betti intIs9
    betti intersect(intIs9,first cI8)
    Y=last Ys;
    (numList,adjList,ptsList,I)=adjunctionProcess(last Ys,2);
    numList, minimalBetti I
    (numList,adjList,ptsList,I)=adjunctionProcess(last Ys,3);
    numList, minimalBetti I
    betti(nonHypY=saturate(Y+minors(2,jacobian Y)))
    dim nonHypY, degree nonHypY
    betti(nonHypYr=radical nonHypY)
    degree nonHypYr, betti nonHypYr
    elapsedTime betti(singY=saturate trim(Y+minors(3,jacobian Y)))  -- 80.2977 seconds elapsed
    dim singY == 1
    elapsedTime betti(singYr=radical singY)
    singYr==nonHypYr
    elapsedTime betti(singI=saturate trim(I+minors(3,jacobian I))) 
    dim singI, degree singI
    elapsedTime betti(singIr=radical singI)  -- 229.098 seconds elapsed
    dim singIr, degree singIr, genus singIr
    minimalBetti singIr, codim singIr
    elapsedTime csingIr=decompose singIr;
    apply(csingIr,c->(dim c, degree c))
    betti(embeddedPart=singI:singIr)
    dim embeddedPart, degree embeddedPart
    betti saturate ptsList_0, degree ptsList_0, dim ptsList_0
    betti saturate ptsList_1, degree ptsList_1, dim ptsList_1
    betti saturate ptsList_2, degree ptsList_2
    betti(fcurve= res singIr)
    betti(adj=adjointMatrix(fcurve.dd_4,symbol t)) 
    betti(planeModel=ann coker adj)
    betti(singPlaneModel=saturate ideal jacobian planeModel)
    dim singPlaneModel, degree singPlaneModel
    decompose singPlaneModel
    kke=GF(char kk,4,Variable=>e)
    P2e=kke[support planeModel]
    cplaneModel=decompose sub(planeModel,P2e)
    tally apply(cplaneModel,c->(dim c, degree c, betti c))
    P5e=kke[support singIr]; dim P5e==6
    csingIr=decompose sub(singIr,P5e);
    tally apply(csingIr,c->(dim c, degree c ,betti c, dim (c+minors(4,jacobian c))))
    matrix apply(csingIr,c->apply(csingIr,d->degree(c+d)))
    "
    )

///
kk=QQ
Z=maximalExtensionOfReyeFanoModel(kk,symbol z)
P9=ring Z
ht=9
M=matrix apply(10,i->apply(4,j->random(ZZ,Height=>ht)-floor(ht/2)))
L=ideal(vars P9*M)
Y=ideal(gens Z%L);
Y=sub(Y,kk[support Y]);
P5=kk[y_0..y_5]
Y=sub(Y,vars P5)
 -- elapsedTime betti(J=trim J) -- 8089.26 seconds elapsed
isHomogeneous J 
elapsedTime betti(f20=eliminate(J,(gens G36)_{1..8}))
T=QQ[t]
support f20
f20t=(sub(sub(f20,kk[support f20]),vars T))_0
toString f20t

f20=259001703048254468280515522016795005842961274121092335548568983215983072254155638963577629962688*t^20-4780817963804210764770703166561236892254036375073927825530301655494948148857044727008276177192672*t^19+
      2753723279554329124179732425356117305738115657635548663253835236511301906745155671209641160258944*t^18+51814187931911875300246076821597106379419443181434146392418694553407058332412714290256175717679656*t^17+
      219227831619352228200849980897275002292080980497759906706871014003240439557484733947030127091761180*t^16-44707810547396039123100351298557127320693676371988584817707334748205678654993288933387105193588872*t^15+
      328477783214705976555984930055208554312149959950930764578444481935266787010794906253890400967333636*t^14+2680465266346711807973934807598656966616517738597311628425367858862245151987128145334322438759778480*t^13-
      3617821380905701399302659050507762348375666105651423750009899301309248236238912583634248614068390504*t^12+10234205193744649244218800498244565248681572903236385042587255325173340274977770690387687754192504956*t^11-
      11299118901605577096526499150509589097944005940524241730096930057693567854181330402368689937274759344*t^10+4155650861732701670939988370682198086597655718515954026985342942492962649594917606005006865046394660*t^9+
      13885767106419104023079209453177555340408202038131778987973144810223886647438431420471676241531638456*t^8-21936007665591462660280743328179956412949772939781878546997741286562502286663644870625333263527038800*t^7+
      6939383286502534942954389069463486654842425486580702445908207056503094232084080096010504519089509202*t^6+6115173886535571867719031799808202428474661193350479023973769902335139213259919793010736361634609804*t^5-
      98685525284398553748543937199068984082546051157053989232431844309694371055324633425326638954840158*t^4-3211316095960136187992991046120978872389643181602755106043200984830783471660320821226255717851048352*t^3+
      276452020705253504233805120970634084755937089111346153302772660905834995739695098451236752068988298*t^2+530051427055608138945481490462770505497583109144849826524472172210524539208641577392322478006541868*t+
      105382630504165281949747011337839643521390160308467951827263550368508128266144709668285914491939161

f20=259001703048254468280515522016795005842961274121092335548568983215983072254155638963577629962688*t^20-4780817963804210764770703166561236892254036375073927825530301655494948148857044727008276177192672*t^19+2753723279554329124179732425356117305738115657635548663253835236511301906745155671209641160258944*t^18+51814187931911875300246076821597106379419443181434146392418694553407058332412714290256175717679656*t^17+219227831619352228200849980897275002292080980497759906706871014003240439557484733947030127091761180*t^16-44707810547396039123100351298557127320693676371988584817707334748205678654993288933387105193588872*t^15+328477783214705976555984930055208554312149959950930764578444481935266787010794906253890400967333636*t^14+2680465266346711807973934807598656966616517738597311628425367858862245151987128145334322438759778480*t^13-3617821380905701399302659050507762348375666105651423750009899301309248236238912583634248614068390504*t^12+10234205193744649244218800498244565248681572903236385042587255325173340274977770690387687754192504956*t^11-11299118901605577096526499150509589097944005940524241730096930057693567854181330402368689937274759344*t^10+4155650861732701670939988370682198086597655718515954026985342942492962649594917606005006865046394660*t^9+13885767106419104023079209453177555340408202038131778987973144810223886647438431420471676241531638456*t^8-21936007665591462660280743328179956412949772939781878546997741286562502286663644870625333263527038800*t^7+6939383286502534942954389069463486654842425486580702445908207056503094232084080096010504519089509202*t^6+6115173886535571867719031799808202428474661193350479023973769902335139213259919793010736361634609804*t^5-98685525284398553748543937199068984082546051157053989232431844309694371055324633425326638954840158*t^4-3211316095960136187992991046120978872389643181602755106043200984830783471660320821226255717851048352*t^3+276452020705253504233805120970634084755937089111346153302772660905834995739695098451236752068988298*t^2+530051427055608138945481490462770505497583109144849826524472172210524539208641577392322478006541868*t+105382630504165281949747011337839643521390160308467951827263550368508128266144709668285914491939161




LCM=sub(lcm (flatten (entries (coefficients f20t)_1))_{0,19},ZZ)
pn=2
primes=select(apply(200,n->(pn=nextPrime(pn+1);pn)),p->not LCM%p==0);#primes
tally apply(primes,p-> (
	cF=decompose ideal sub(f20t,ZZ/p[t]);
	if sum(cF,c->degree c)==20 then ( 
	    tal=tally apply(cF,c->degree c);
	    evenKeys=select(keys tal,k->k%2==0);
	    (sum(evenKeys,k->tal#k))%2) else (print p;0)  
	))
 
tally apply(primes,p-> (
	cF=decompose ideal sub(f20t,ZZ/p[t]);
	tal=if sum(cF,c->degree c)==20 then ( 
	    tally apply(cF,c->degree c)) else(p, "ramified")))   

///



analyseFanoPolarizedEnriquesSurface=method()
analyseFanoPolarizedEnriquesSurface(Ideal) := Y -> (
    print"
    P5:=ring Y;
    assert(dim P5==6);
    kk:=coefficientRing P5;
    assert(degree Y==10 and dim Y==3)
    G36:=kk[a_(0,0)..a_(2,2)]
    A:=transpose genericMatrix(G36,a_(0,0),3,3)
    sA:=A|diagonalMatrix({1,1,1})
    s= symbol s
    P2:=kk[s_0..s_2]
    P2xG36:=P2**G36
    betti(flag=sub(vars P2,P2xG36)*sub(sA,P2xG36)) 
    betti(Yf=sub(Y,flag))
    betti(m10x10=sub(contract(transpose sub(basis(3,P2),P2xG36),gens Yf),G36))
    betti(m10x10=map(G36^10,,sub(m10x10,G36)))
    elapsedTime betti (J=minors(2,m10x10)) -- 0.768897 seconds elapsed
    elapsedTime betti(J=trim J)  -- 1480.41 seconds elapsed for general Enriques

    elapsedTime betti(gbJ=gens gb( J,DegreeLimit=>6))   -- 86.3892 seconds elapsed
    dim J==0, degree J==20
    betti(J=trim ideal gbJ)
    elapsedTime cJ=decompose J;
    tally apply(cJ,c->(dim c, degree c))
    r=lcm apply(cJ,c->degree c)
    kke=GF(char kk,r,Variable=>symbol e)
    P5e=kke[gens P5]
    Ye=sub(Y,P5e);
    G36e=kke[gens G36]
    cJe=decompose sub(J,G36e);
    tally apply(cJe,c->(degree c, dim c))
    sAe=sub(sA,G36e);
    planeCubics=apply(cJe,c->(plane=ideal(vars P5e*sub(syz(sAe% c),kke));trim(plane+Ye)));
    tally apply(planeCubics,c->(dim c, degree c, betti c)) 
    L=matrix apply(planeCubics,c->apply(planeCubics,d->(if dim(c+d)==0 or dim(c+d)==2 then 0 else 1)))
    sL=LLL syz L
    ind={}
    scan(10,j->(pair=select(20,i->not sL_(i,j)==0);ind=ind|pair))
    ind
    L_ind^ind
    ind2={0,2,4,6,8,10,12,14,16,18}
    L2=(L_ind^ind)_ind2^ind2
    tenCubics=planeCubics_ind_ind2;
    betti(cub11=intersect tenCubics)
    ind1=if degrees source gens cub11==toList(11:{3}) then ind else ind_({1,0}|toList(2..19));
    tenCubics=planeCubics_ind1_ind2;    
    betti intersect tenCubics
    pencils=apply(tenCubics,F->(F2=saturate(F^2+Ye);
	    h=F2_0;
	    residual=(ideal h +Ye):F2;
	    (gens residual)_{0,1}));
    tally apply(pencils,p->betti p)
    baseLoci=apply(pencils,p->saturate(ideal p +Ye));
    tally apply(baseLoci,b->(dim b, degree b, genus b, betti b))
    elapsedTime singBs=apply(baseLoci,b->trim(b+minors(4,jacobian b)));
    tally apply(singBs,c->dim c)
    tally apply(baseLoci,b->(twoB=saturate(b^2+Ye);(dim twoB,degree twoB,genus twoB)))
    betti res first baseLoci
    -- 14+1-9, binomial(5+2,2)-(28+1-9)
    -- 14*t+1-9+14*(t-1)+1-9 + deg NormalBundle == 28*t +1 -33
    --14+2*9-1-33
    -- t+1+(t+2+1)==2t+1-(-3) => in case of a nodal Enriques, 
    --                           the self-intersection numbers of the b's are -2
    matrix apply(tenCubics,c->apply(baseLoci,b->degree(c+b)))
    M=matrix apply(baseLoci,b1->apply(baseLoci,b2->if dim(b1+b2)==1 then degree(b1+b2) else
	    if dim(b1+b2)==2 then -2 else 0))
    eigenvalues(M**RR)
    factor det M
    L2
    det L2
    eigenvalues L2
    "
    )

identifyMaximalExtension=method()
identifyMaximalExtension(Ring,ZZ) := (kk,k2) -> (  
    if k2==0 then (
	print "
	X:=maximalExtensionOfReyeFanoModel(kk,symbol z)
	P9:=ring X;
	P3:=kk[x_0..x_3];
	h1:=(basis(2,P3))_{0,1,4,2,5,7,3,6,9,8};
	D:=diagonalMatrix({1,1,-1,1,1,-1,1,1,-1,1})
	P3y:= kk[y_0..y_3];
	hy:=sub(h1*D,vars P3y);
	hx:=sub(hy, vars P3);
	P3xP3:=P3**P3y;
	hxhy:=sub(hx,P3xP3)+sub(hy,P3xP3)
	betti(secV2P3:=ker map(P3xP3,P9,hxhy))
	assert(secV2P3==X);
	P333=kk[x_0..z_3]
	hx=basis(2,P3)
	Sec3=ker map(P333,P9,sub(hx,P333)+sub(hx,(vars P333)_{4..7})+sub(hx,(vars P333)_{8..11}))
	cre = map(P9^1,,(transpose jacobian Sec3)*diagonalMatrix{2,1,1,1,2,1,1,2,1,2})
	betti(cre2=map(P9^1,, sub(cre,cre)))
    	saturate ideal cre2== Sec3^2
    	-- Sec3 induces a self-dual Cremona transformation whose base loci is secV2P3
	-- according to [ESB]
    	betti(cre=map(P9^1,,(transpose jacobian q)))
    	P9w=kk[w_0..w_9]
	P9xP9=P9**P9w	
    	betti(graph=minors(2,sub(cre,P9xP9)||sub(vars P9w,P9xP9)))
    	tally degrees source gens graph
        betti(g1=graph:ideal sub(cre,P9xP9))
    	tally degrees source gens g1
	betti (creInv=map(P9w^1,,sub(transpose syz diff(sub(vars P9,P9xP9),transpose gens g1),P9w)))
    	betti(idcre=map(P9^1,,sub(creInv,cre)))
	betti (q2=saturate ideal idcre)
    	q2==q^2	   	
    	minimalBetti (singQ=ideal jacobian q)
    	singQ==X	
    	betti (idCreInv=map(P9w^1,,sub(cre,creInv)))
	qw=radical saturate ideal idCreInv
	use P9
	q
	qw
    	q'=sub(sub(q,{z_2=>2*z_2,z_5=>2*z_5,z_0=>2*z_0,z_8=>2*z_8}),vars P9w)
	q'_0-qw_0
	P3z=kk[z_0..z_3]
    	hz=sub(hx,vars P3z)	
    	P3xP3xP3=P3xP3**P3z
	hxyz=sub(hxhy,P3xP3xP3)+sub(hz,P3xP3xP3)
	betti(qq=ker map(P3xP3xP3,P9,hxyz))
	qq==q
	ideal jacobian qq==X
	"
	);    	
    if k2==-5 then (
	print "
	x := symbol x
	P2=kk[x_0..x_2]
    	betti(Y=rationalSurface(P2,6,toList(4:2)|toList(10:1),symbol z))	
    	(A,B,eq)=extension(Y,2);
	assert(eq==0)
        betti(Z=ideal syz transpose A)
    	betti(fZ=res(Z))
	P9=kk[z_0..z_9];dim P9==10
        Z=sub(Z,vars P9);
	betti(fib=trim minors(2,gens Z||random(P9^1,P9^10)))
    	betti(fib1=fib:Z)	
        degree fib1, dim fib1 
	-- => gens Z define a Cremona transformation P9 --> P9	
    	betti(m10x10=jacobian Z)	
    	betti(quintic=ann coker m10x10)
	betti(trim (quintic +Z))
    	P9w=kk[w_0..w_9]
	P9xP9=P9**P9w	
    	betti(graph=minors(2,sub(gens Z,P9xP9)||sub(vars P9w,P9xP9)))
    	tally degrees source gens graph
     	elapsedTime betti(g1=syz(sub(matrix{{Z_0}},P9xP9)|gens graph, DegreeLimit=>{3,3})) -- 320.617 seconds elapsed
    	tally degrees source g1
	betti(g2=trim ideal g1^{0}),tally degrees source gens g2 
	betti(m15x10=map(P9w^15,,sub(diff(sub(vars P9,P9xP9),transpose gens g2),P9w)))
	betti (creInv=map(P9w^1,,sub(transpose syz(m15x10 ,DegreeLimit=>4),P9w)))
    	betti(idcre=map(P9^1,,sub(creInv,gens Z)))
	betti (q2=saturate ideal idcre)
	q2==quintic
	W=ideal creInv;
	minimalBetti W
    	m10x10w=jacobian W;
	betti (quinticW=ann coker m10x10w)
	elapsedTime betti(idcreW=map(map(P9w^1,, sub(gens Z,creInv)))) -- 17.0161 seconds elapsed
	betti (q2W=saturate ideal idcreW)
    	q2W==quinticW
	-- => thus the generators of Z and W define to each other inverse Cremona transformation
	--    of degrees (3,2) with quintic exceptional divisors	
    	betti(fW=res W)
    	dim W, degree W, genera W
	betti(adjW=adjointMatrix(fW.dd_5,symbol x))
	P4=ring adjW,dim P4==5
	betti (para=map(P4^1,,transpose syz transpose adjW))
    	sub(W,para)==0
	-- => para defines a rational parametrization of W by P4
	baseLocus=ideal para;
	minimalBetti baseLocus
	dim baseLocus, degree baseLocus	
	
	-- construction of W and Z over QQ:
       	P4=QQ[x_0..x_4]
	coordinatePts=ideal flatten apply(5,i->apply(i,j->x_i*x_j))
	P9=QQ[w_0..w_9]
	phi=map(P4,P9,gens coordinatePts)
	W=trim ker phi
	betti res W
	quinticW=ann coker (m10x10W=jacobian W)
	P9z=QQ[z_0..z_9]
	P9xP9=P9z**P9
    	betti(graph=minors(2,sub(gens W,P9xP9)||sub(vars P9z,P9xP9)))
	betti(g1=syz(sub(W_0,P9xP9)|gens graph,DegreeLimit=>{3,2}))
	betti(g2=trim ideal g1^{0}), tally degrees source gens g2
	betti(m15x10=map(P9z^15,,sub( diff(sub(vars P9,P9xP9), transpose (gens g2)_{0..14}),P9z)))
	betti (cre1=transpose syz(m15x10,DegreeLimit=>4))
	betti(creId=map(P9z^1,,sub(gens W,cre1)))
	(quintic_0*vars P9z-creId)==0
	betti(creIdw=map(P9^1,,sub(cre1,gens W)))    
    	creIdw-quinticW_0*vars P9
    	Z=ideal cre1
	betti(fZ=res Z)
	quintic=ann coker (m10x10=jacobian Z)
    	betti(singZ=trim(Z+minors(3,jacobian Z)))
	(dim singZ,dim Z)==(3,7) 
	betti(singZr=radical singZ)
	degree singZr
	csingZ=decompose singZr
	tally apply(csingZ,c->(dim c,degree c))
        netList apply(csingZ,c->(dim c,degree c,c))
	
	-- check the adjuction process of a surface section Y
	betti(L=ideal random(P9z^1,P9z^{4:-1}))
	Y=ideal(gens Z%L);
	P5=kk[support Y],dim P5==6
	Y=sub(Y,P5);
	ll=adjunctionProcess Y;
	ll_0, minimalBetti ll_3
	"
	);
    if k2==-4 then (
	setRandomSeed("good start");
	print "   	
        betti(Y=threeRegularSurfaceOfCodim3(-4,kk))
    	(A,B,eq)=extension(Y,2);
        assert(eq==0)
    	betti(Z=ideal syz transpose A)	
    	P7=kk[z_0..z_7]
	Z=sub(Z,vars P7);
    	dim Z, degree Z	
	-- nonHypersurface singularities
	elapsedTime betti( nonHypSing=saturate trim (Z+minors(2,jacobian Z))) -- 5.29736 seconds elapsed
    	dim  nonHypSing, degree nonHypSing, genus nonHypSing
	cnonHypSing=decompose nonHypSing    	
        apply(cnonHypSing, c-> (dim c, degree c, betti c))
	betti (pts6=intersect cnonHypSing_{1..6}) 	
    	dim pts6, degree pts6
	betti(fZ=res Z)	
        betti(adj=adjointMatrix(fZ.dd_3,symbol x))	
    	betti(I=ann coker adj)
	betti (fI=res I)
	dim I, dim Z
	P5=ring I
	m6x6=sub(jacobian ideal fI.dd_2,kk)
	betti(aut=map(P5^1,,vars P5*inverse m6x6))
	adj=sub(adj,aut)
	I= ann coker adj
	PI=P5/I
	
	betti(fadj=res coker transpose (adj**PI))
	rank fadj.dd_2
	betti(singBundle=minors(2,fadj.dd_2))
	betti(sB=saturate trim(sub(singBundle,P5)+I))
	dim sB, degree sB
    	csB=decompose sB
	pts=apply(csB,c-> sub(syz transpose jacobian c,kk))
	fibs=apply(pts,pt->trim ideal (fZ.dd_3*(inverse transpose m6x6)*pt));
    	tally apply(fibs,f->(dim f, degree f))
        --=> there are six fibers, which are P3's
	betti(intFib=intersect fibs)
    	ideal (gens intFib)_{0..9}==Z
	-- these six P3's determine Z 	
    	matrix apply(fibs,F->apply(fibs,F1->dim(F+F1)))
    	-- they are disjoint
	matrix apply(fibs,F->apply(cnonHypSing,c->dim (c+F)))
	-- the singular line intersect each of the P3's, each P3 contains one singular point.
     	betti(sixPts=trim sub(sB,b11))
    	betti(sixPtsat=saturate(saturate(sixPts,ideal basis({1,0},P1xP2)),ideal basis({0,1},P1xP2)))
    	tally degrees source gens sixPtsat
	-- => the six Points project to different points on the factors
	betti sixPtsat
	
    	
    	P1xP2=kk[s_0,s_1,t_0..t_2,Degrees=>{2:{1,0},3:{0,1}}]
    	b11=basis({1,1},P1xP2)
	sub(I,b11)
	betti(adj1=map(P1xP2^15,,sub(fadj.dd_1,b11)))
	betti (sadj1=syz adj1), tally degrees source sadj1, tally degrees target sadj1
	
	-- construction of Z
	P1BundleOverP1xP2=kk[u_0,u_1,s_0,s_1,t_0..t_2,Degrees=>{{1,0,0},{1,0,2},2:{0,1,0},3:{0,0,1}}]
	basis({1,1,2},P1BundleOverP1xP2)
    	sixPoints=apply(6,i->ideal random(P1BundleOverP1xP2^1,P1BundleOverP1xP2^{{0,-1,0},2:{0,0,-1},-{1,0,2}}))	
    	betti (sixPts=intersect sixPoints), tally degrees source gens sixPts
    	betti (g=gens intersect(sixPts,ideal(basis({1,1,2},P1BundleOverP1xP2))))
	g
        paraZ=map(P1BundleOverP1xP2,P7,g) 	
    	betti(Z=trim ker paraZ)		
    	minimalBetti Z
	
	-- analyse paraZ 	
	elapsedTime betti( nonHypSing=saturate trim (Z+minors(2,jacobian Z))) -- 5.29736 seconds elapsed
    	dim  nonHypSing, degree nonHypSing, genus nonHypSing
	cnonHypSing=decompose nonHypSing    	
    	preImages=apply(cnonHypSing,c->(ideal(g*sub(syz transpose syz transpose jacobian c,kk)):ideal g));
        preImagesSat=apply(preImages,c->
	    saturate(saturate(saturate(c,ideal(u_0,u_1)),ideal(s_0,s_1)),ideal(t_0,t_1,t_2)));	
        tally apply(preImagesSat,c-> tally degrees source gens c)	
        decompose first preImagesSat
	last preImagesSat, apply(select(sixPoints, p-> trim(p+last preImages)==p),p->trim p)
	-- => paraZ collapes the fiber of the P1BundleOverP1xP2 which contains one ot the points
	--    it also collaps the section defined by u_0=0 to the line
	first cnonHypSing, g%ideal u_0
	-- determine the nonregular locus of paraZ
	rank jacobian ideal g
    	elapsedTime betti(nonReg=trim minors(5,jacobian ideal g))
	betti (nonRegSat=saturate(saturate(saturate(nonReg,ideal(u_0,u_1)),ideal(s_0,s_1)),ideal(t_0,t_1,t_2)))	
	nonRegSatMinusExceptionalSet=nonRegSat;
	scan(preImagesSat,c->nonRegSatMinusExceptionalSet=nonRegSatMinusExceptionalSet:c);
	badLocus=(nonRegSatMinusExceptionalSet:ideal u_0);
	badLocus+sixPts==sixPts
	
	elapsedTime betti(singZ = trim(Z+minors(3,jacobian Z))) -- 2510.26 seconds elapsed
	elapsedTime betti(singZr=radical saturate singZ)
    	dim singZr, degree singZr
	singZr==radical nonHypSing
	
	Y = ideal(gens Z%ideal random(P7^1,P7^{2:-1}));P5=kk[support Y];Y=sub(Y,P5);
    	ll=adjunctionProcess Y;        
        ll_0,minimalBetti ll_3
	
	P2=kk[x_0..x_2]
	Y'=rationalSurface(P2,7,{3}|toList(6:2)|toList(6:1),P5);
	ll=adjunctionProcess Y';        
        ll_0,minimalBetti ll_3
	-- dimension count
	dimAutP1BundelOverP1xP2=3+8+binomial(2+2,2)+1
	dimG28=2*6
	6*4-dimAutP1BundelOverP1xP2+dimG28, 13*2-8
	"
	);
    if k2==-2 then (
	setRandomSeed("start with the same");
	print "
	betti(Y=threeRegularSurfaceOfCodim3(-2,kk))
    	(A,B,eq)=extension(Y,2);
        assert(eq==0)
    	betti(Z=ideal syz transpose A)	
    	P6=kk[z_0..z_6]; dim ring Z==7; Z=sub(Z, vars P6);
	betti(fZ=res Z)
    	betti(adj=adjointMatrix(fZ.dd_3,symbol x))	
    	betti(I=ann coker adj)
	minimalBetti I
    	P5=ring Y
	dim Y
	dim I, dim Z
	P5=ring I
	betti(singI=trim(I+minors(2,jacobian I)))
	dim singI, degree singI
	minimalBetti (singIs=saturate singI)
	csingIs=decompose singIs 
	tally apply(csingIs,c->(dim c, degree c))
    	sixPoints=apply(csingIs,c->syz transpose jacobian c) 
    	M=first sixPoints
	scan(5,i->M=M|sixPoints_(i+1));
	aut=vars P5* transpose M
	adj=sub(adj,aut)
	betti(I=trim ann coker adj)
	I	
	PI=P5/I	
    	betti(sadjt=syz transpose (adj**PI))
	minors(2,sadjt)==0
	betti(baseLocus=trim ideal sadjt)
	betti(bsLocus=saturate trim(I+sub(baseLocus,P5)))
	degree bsLocus, dim bsLocus
    	elapsedTime cbsLocus=decompose bsLocus;#cbsLocus
    	tally apply(cbsLocus,c->(dim c, degree c, betti c))	
    	intersect(cbsLocus)==bsLocus
	I
	cbsLocus
        D=diagonalMatrix (reverse (entries (jacobian last cbsLocus)^{5})_0|{-1})
	aut2=vars P5 * D
	I2=trim sub(I,aut2)
	trim sub(last cbsLocus,aut2)
    	adj2=sub(adj,aut2)
	PI2=P5/I2
	betti(sadjt=syz transpose (adj2**PI2))
	minors(2,sadjt)==0
	betti(baseLocus=trim ideal sadjt)
	betti(bsLocus=saturate trim(I2+sub(baseLocus,P5)))
	degree bsLocus, dim bsLocus
    	elapsedTime cbsLocus=decompose bsLocus;#cbsLocus
    	tally apply(cbsLocus,c->(dim c, degree c, betti c))
	netList cbsLocus	
    	intersect(cbsLocus)==bsLocus
	I2
        singI2=trim(I2+minors(2,jacobian I2))
	decompose singI2
	cbsLocus
	netList decompose (ideal sub(sadjt_{0},P5)+I2)
    	
	use P5
    	m4x4=matrix{{0,x_1,x_2,x_3},{-x_1,0,x_0,x_5},{-x_2,-x_0,0,x_4},{-x_3,-x_5,-x_4,0}}
        pfaffians(4,m4x4),I2
	trim (I2+ pfaffians(4,m4x4))   
        netList cbsLocus_{3,1,0,2}, m4x4
    	-- parameterCount matches
	4*2+6,2*11-8
	cbsLocus
    	netList (cms=apply(4,i->(m=trim ideal sadjt_{i};primaryDecomposition m))) 	
    	apply(cms,cm->betti intersect cm)
	netList apply(cms,cm -> tally apply(cm,c->(dim c, degree c, degree radical c ,betti c)))
	netList(cms3= apply(cms,cm->select(cm,c->dim c==3)))
	m4x4a=matrix{{0,-x_4,x_5,-x_0},{x_4,0,-x_3,x_2},{-x_5,x_3,0,-x_1},{x_0,-x_2,x_1,0}}
    	-- m4x4 and m4x4a are only used to describe the patern of base loci    
        m4x4*m4x4a
	-- the choice of a description of the rational map V(I2) - - > Z
	-- depends on the choice of an index i in {0,1,2,3}
	Zs=apply(4,i->(
		three=delete(i,{0,1,2,3});
	    a=apply(three,j->trim (ideal random(1,P5)+ideal(m4x4_{j})));
	    b={trim (ideal(random(1,P5)%ideal(m4x4_{i}))+(ideal(m4x4_{i}))^2)};
    	    c=apply(three,j->trim ideal(m4x4a_{j}))|{trim ideal m4x4_{i}};
            d={trim ideal flatten apply(6,i->apply(i,j->x_i-x_j))};
            betti(h=intersect(a|b|c|d));
	    h=mingens ideal(gens h %I2);
    	    Z=trim ker map(PI2,P6,h)));
    	tally apply(Zs,Z-> minimalBetti Z)
	Z=last Zs;
    	Y=ideal(gens Z % ideal random(1,P6));P5z=kk[support Y];Y=sub(Y,P5z);
    	ll=adjunctionProcess(Y);
        ll_0,minimalBetti ll_3	
	elapsedTime betti (singZ=trim(Z+minors(3,jacobian Z))) -- 106.718 seconds elapsed
	dim singZ, degree singZ
	betti(singZr=radical singZ)
	degree singZr
	csingZr=decompose singZr
	pts=apply(csingZr,c->sub(syz transpose jacobian c,kk))
	
	preImages=apply(4,i->(ideal(h*syz transpose pts_i)+I2):(ideal h+I2))
	m4x4
	-- => the pre images are the planes defined by the rows of m4x4
    	apply(preImages,plane->h%plane)
	-- => They map to points. The choice of the decription of the rational map 
	--    has one of these planes as base loci.
	
	isHomogeneous cp0
	cp0_0
	support cp0
	P5z1=kk[support cp0]
	Ys=sub(cp0,P5z1);
	betti(Ys2=(gens Ys%(ideal vars P5z1)^3))
	betti(Ys2a=gens Ys*syz Ys2)
	Ys3=trim (ideal(Ys2a)+ideal Ys2)
    	betti(Ys3=trim (Ys+Ys2) ) 
	Ys3== ideal Ys2
	minimalBetti Ys3
    	dim Ys3, degree Ys3
	-- => Z has 4 singular points p in which (Z,p) is analytically
	--    isomorphic to the cone over the Veronese surface in P5	
	 
     	"
       );
   )

extensionsOfSpecialCurves=method()
extensionsOfSpecialCurves(Ring,ZZ) := (kk,k2) -> (
    if k2==-2 then (
	print "
    Y= threeRegularSurfaceOfCodim3(k2,kk);
    P5=ring Y;assert(dim P5==6)    
    H=ideal random(1,P5);
    C= ideal(gens Y%H);
    P4= kk[support C];
    C=sub(C,P4);
    (A,B,eq) = extension(C,2);
    dim ring A
    elapsedTime minimalBetti eq -- 5.77506 seconds elapsed
    betti (feq=res(eq,FastNonminimal=>true))
    betti(I5=ann coker transpose feq.dd_9)
    dim I5, degree I5    
    elapsedTime betti(rest1=eq:I5)   -- 33.3723 seconds elapsed  
    elapsedTime minimalBetti rest1
    betti(frest1=res(rest1,FastNonminimal=>true))    
    elapsedTime betti(cycles= syz transpose frest1.dd_8)
    betti(ext7=prune subquotient(cycles, transpose frest1.dd_7))        
    betti(I7=ann ext7)    
    dim I7, degree I7    
    betti(I9=rest1:I7)    
    dim I9, degree I9    
    minimalBetti I9
    cI9=decompose I9    
    apply(cI9,c->(dim c, degree c ,betti c))
    I9=first cI9;
    I6=last cI9 
    elapsedTime eq == intersect(I9,I7,I6,I5)   -- 13.315 seconds elapsed 
    degree I9, degree I7      
    betti(Z6=ideal syz (transpose A%I6))    
    P6=kk[support Z6]; dim P6==7
    betti(Z6=sub(Z6,P6))
    betti(Y6=ideal(gens Z6%ideal random(1,P6)))    
    P5=kk[support Y6]; dim P5==6
    Y6=sub(Y6,P5);
    (numList,adjList,ptsList,I)=adjunctionProcess(Y6,1);       
    numList, minimalBetti I 
    dim I5, degree I5, codim I5   
    elapsedTime minimalBetti I5
    betti(fI5=res(I5,FastNonminimal=>true))
    betti(cycles=syz transpose fI5.dd_10)    
    betti(ext9=prune subquotient(cycles, transpose fI5.dd_9))
    betti(adj=adjointMatrix(transpose presentation ext9, symbol z))    
    betti (fadj=res coker adj)
    betti(I5a=ideal fadj.dd_5)    
    minimalBetti I5a        
    elapsedTime cI5a=decompose I5a;
    apply(cI5a,c->(dim c, degree c))    
    cI5a1=select(cI5a,c->degree c == 1)    
    pI5a1=apply(cI5a1,c->sub(syz transpose jacobian c,kk))    
    I5s=apply(pI5a1,c-> trim ideal(transpose presentation ext9*c));   
    Y5s=apply(I5s,c->(Y=ideal syz (transpose A%c);P5=kk[support Y];Y=sub(Y,P5)));
    dim I7, degree I7 , genus I7, codim I7
    elapsedTime minimalBetti I7
    elapsedTime betti(fI7=res(I7,FastNonminimal=>true))  
    betti(cycles=syz transpose fI7.dd_8)
    elapsedTime betti(ext7=prune subquotient(cycles,transpose fI7.dd_7))
    betti(adj=adjointMatrix(transpose presentation ext7,symbol z))      
    betti (fadj=res coker adj)
    betti(I7a=ann coker transpose fadj.dd_4)
    elapsedTime (cI7a=decompose I7a) 
    apply(cI7a,c->(dim c, degree c))
    cI7a1=select(cI7a,c->degree c==1)
    pI7a1=apply(cI7a1,c->sub(syz transpose jacobian c,kk))    
    I7s=apply(pI7a1,c-> trim ideal(transpose presentation ext7*c));   
    Z7s=apply(I7s,c->(Y=ideal syz (transpose A%c);P=kk[support Y];Y=sub(Y,P)));   
    Y7s=apply(Z7s,Z->(P= ring Z; Y=ideal(gens Z%ideal random(P^1,P^{2:-1}));
	    P5=kk[support Y];Y=sub(Y,P5)));
    Z9=ideal syz (transpose A%I9);P9=kk[support Z9];betti(Z9=sub(Z9,P9))
    Y9= ideal( gens Z9%ideal random(P9^1,P9^{4:-1}));P5=kk[support Y9];Y9=sub(Y9,P5);
    Ys={Y9}|Y7s|{Y6}|Y5s;    
    netList apply(Ys,Y->((numList,adjList,ptsList,I)=adjunctionProcess(Y,1);
	    (numList, minimalBetti I)))    
    "
    );
 if k2==-1 then (
	print "
    Y= threeRegularSurfaceOfCodim3(k2,kk);
    P5=ring Y;assert(dim P5==6)    
    H=ideal random(1,P5);
    C= ideal(gens Y%H);
    P4= kk[support C];
    C=sub(C,P4);
    (A,B,eq) = extension(C,2);
    dim ring A
    elapsedTime minimalBetti eq ---- 35.9788 seconds elapsed
    betti (feq=res(eq,FastNonminimal=>true))
    elapsedTime betti(I5=ann coker transpose feq.dd_9)
    dim I5, degree I5    
    elapsedTime betti(rest1=eq:I5)  -- 27.3437 seconds elapsed
    elapsedTime minimalBetti rest1
    betti(frest1=res(rest1,FastNonminimal=>true))           
    betti(I7=ann coker transpose frest1.dd_7)    
    dim I7, degree I7    
    betti(I9=rest1:I7)    
    dim I9, degree I9
    dim I7, degree I7 , genus I7, codim I7
    elapsedTime minimalBetti I7
    elapsedTime betti(fI7=res(I7,FastNonminimal=>true))     
    elapsedTime betti(cycles=syz transpose fI7.dd_8)
    elapsedTime betti(ext7=prune subquotient(cycles,transpose fI7.dd_7))
    betti(adj=adjointMatrix(transpose presentation ext7,symbol z))      
    betti (fadj=res coker adj)
    betti(I7a=ann coker transpose fadj.dd_4)
    elapsedTime (cI7a=decompose I7a) 
    apply(cI7a,c->(dim c, degree c))
    cI7a1=select(cI7a,c->degree c==1)
    pI7a1=apply(cI7a1,c->sub(syz transpose jacobian c,kk))    
    I7s=apply(pI7a1,c-> trim ideal(transpose presentation ext7*c));   
    Z7s=apply(I7s,c->(Y=ideal syz (transpose A%c);P=kk[support Y];Y=sub(Y,P)));   
    Y7s=apply(Z7s,Z->(P= ring Z; Y=ideal(gens Z%ideal random(P^1,P^{2:-1}));
	    P5=kk[support Y];Y=sub(Y,P5)));
    elapsedTime minimalBetti I5
    betti(fI5=res(I5, FastNonminimal=>true))
    betti(m90x11=fI5.dd_9^{6..95})
    betti(adj=adjointMatrix(m90x11,symbol z))
    elapsedTime betti(I5a= ann coker transpose syz transpose syz adj)
    dim I5a, degree I5a
    elapsedTime cI5a=decompose I5a;
    apply(cI5a,c->(dim c, degree c))
    cI5a1=select(cI5a,c->degree c==1);
    pI5a1=apply(cI5a1,c->sub(syz transpose jacobian c,kk))    
    I5s=apply(pI5a1,c-> trim ideal(m90x11*c));   
    Y5s=apply(I5s,c->(Y=ideal syz (transpose A%c);P5=kk[support Y];Y=sub(Y,P5)));
    Ys={Y9}|Y7s|Y5s;
    tally apply(Ys,Y->((numList,adjList,ptsList,I)=adjunctionProcess(Y,1);
	    (numList, minimalBetti I)))
    "
    );
)


    
specialFamiliesOfSommeseVandeVen=method()
specialFamiliesOfSommeseVandeVen(Ring,ZZ) := (kk,fam) -> (
    assert(member(fam,{1,2,3,4}));
    t := symbol t;
    P2 := kk[t_0..t_2];Y:=null;
    x := symbol x;
    if fam==1 then Y=rationalSurface(P2,6,toList(7:2),x);
    if fam==2 then Y=rationalSurface(P2,6,toList(7:2)|{1},x);
    if fam==3 then Y=rationalSurface(P2,9,toList(8:3),x);
    if fam==4 then (
	h:=matrix{{t_0^2,t_1^2,t_2^2,t_0*t_1-t_0*t_2,t_1*t_2-t_0*t_2}};
	y := symbol y;
	P4:=kk[y_0..y_4];
	veronese:=ker map(P2,P4,h);
	ci := ideal (gens veronese*random(source gens veronese,P4^{2:-3}));
	X:=ci:veronese;plane:=null;fivePts:=null;pts:=null;pt:=null;
	tangPlane:=null; ctp:=null;
	Lines:=apply(2,i->(
		while( plane=ideal random(P4^1,P4^{2:-1});
	    	    fivePts=decompose(plane+X);
 	    	    pts=select(fivePts,c->(dim c, degree c)==(1,1));
	    	    #pts==0 ) do ();
	pt=transpose syz transpose jacobian first pts;
	tangPlane=vars P4*syz transpose syz transpose  sub(jacobian X,pt);
	ctp=decompose (ideal(tangPlane*random(kk^2,kk^1))+X);
	line:=first ctp
	));
        H:=(intersect Lines)_0;
	B:=last decompose(ideal H+X);
	betti(threeB:=saturate(B^3+X));
	H3:=threeB_0;
	betti(residual:=(ideal H3+X):threeB);
	betti(h=gens trim ideal (gens residual % X));
	P5:=kk[x_0..x_5];
	PX:=P4/X;
	phi:=map(PX,P5,h);
	betti(Y=trim ker phi));
    return Y)

///
t := symbol t;
P2 := kk[t_0..t_2]
h:=matrix{{t_0^2,t_1^2,t_2^2,t_0*t_1-t_0*t_2,t_1*t_2-t_0*t_2}};
y = symbol y;	
P4=kk[y_0..y_4];
Y=ker map(P2,P4,h);
adjunctionProcess(Y)
betti(omegaY=Ext^1(module Y,P4^{-4}))
P5=kk[x_0..x_5]
m=matrix{{x_0,x_1,x_3,x_4},{x_1,x_2,x_4,x_5}}
Y=minors(2,m)
degree Y, dim Y
adjunctionProcess Y
pts=oo_2_0
expectedDimension(6,toList(4:2)|toList(6:1))
Y=rationalSurface(P2,6,toList(4:2)|toList(6:1),symbol y);
P9=ring Y
PY=P9/Y
phi=map(PY,P5,random(P9^1,P9^{6:-1}));
betti(I=trim ker phi)
minimalBetti I
codim I
betti (omegaY=Ext^2(module I, P5^{-6}))
(J,adj)=slowAdjunctionCalculation(I,transpose presentation omegaY,symbol u);
minimalBetti J
///



paracanonicalEmbeddedPlaneQuintic=method()
paracanonicalEmbeddedPlaneQuintic(Ring) := kk -> (
    t := symbol t;
    P2:=kk[t_0..t_2];
    -- compute the linear system |O_C(D)| of 10 points on a plane quintic C
    -- we pick the residual 10 points of the complete intersection of C with a quartic
    -- through D first via a Hilbert Burch matrix
    m5x5:=random(P2^5,P2^{5:-1});
    C:=ideal det m5x5;    
    PC:= P2/C;
    h:=map(P2^1,,transpose syz (m5x5)^{1..4});
    x:=symbol x;
    P4:=kk[x_0..x_4];
    I:=trim ker map(PC,P4,h);    
    assert((dim I, degree I, genus I)==(2,10,6));
    I)

prymCanonicalEmbeddedPlaneQuintic=method()
prymCanonicalEmbeddedPlaneQuintic(Ring) := kk -> (
    t := symbol t;
    P2:=kk[t_0..t_2];
    -- use a self-lnked collection of to points obtained from
    -- a symmetric 5x5 matrix
    m5x5a:=random(P2^5,P2^{5:-1});
    m5x5:=m5x5a+transpose m5x5a;
    C:=ideal det m5x5;    
    PC:= P2/C;
    h:=map(P2^1,,transpose syz (m5x5)^{1..4});
    x:=symbol x;
    P4:=kk[x_0..x_4];
    I:=trim ker map(PC,P4,h);    
    assert((dim I, degree I, genus I)==(2,10,6));
    I)


------------ Tests ------------------
TEST///
kk=ZZ/nextPrime(10^3)
P2=kk[x_0..x_2]
L=toList(4:2)|toList(10:1)
Y=rationalSurface(P2,6,L,symbol y);
minimalBetti Y
dim Y
(A,B,eq)=extension(Y,2);
assert(eq==0)
///



TEST///
kk=ZZ/nextPrime(10^3)
L=listOfN33Surfaces(kk);
netList apply(L,(k2,Y)->((A,B,eq)=extension(Y,2);
	(numList,adjList,ptsList,I)=adjunctionProcess(Y,1);
	(k2,eq,dim ring A-dim ring Y, numList, minimalBetti I)))
///

TEST///
kk=ZZ/nextPrime(10^3)
(J,p)=fanoPolarizedEnriquesSurface(kk,symbol z); 
minimalBetti J
assert(p+J==p)
(A,B,eq)=extension(J,2);
assert(eq==0)
assert(dim ring A==dim ring J)
///

TEST ///
kk=ZZ/nextPrime(10^3)
P2=kk[t_0..t_2]
d=9
L=toList(4:4)|toList(3:2)
expectedDimension(d,L)
betti (H=linearSystemOnRationalSurface(P2,d,L))
assert(expectedDimension(d,L)==rank source H)
x= symbol x
betti(J=rationalSurface(P2,d,L,x))
assert(degree J== d^2-sum(L,r->r^2))
minimalBetti J -- explain this special case
d=9
L=toList(5:3)|toList(6:2)
n=expectedDimension(d,L)-1
x=symbol x
Pn=kk[x_0..x_n]
betti(J=rationalSurface(P2,d,L,Pn))
assert(degree J== d^2-sum(L,r->r^2))
minimalBetti J
///

TEST ///

kk=ZZ/nextPrime(10^3)
P2=kk[t_0..t_2]
d=9
L=toList(5:3)|toList(6:2)
n=expectedDimension(d,L)-1
x=symbol x
Pn=kk[x_0..x_n]
betti(J=rationalSurface(P2,d,L,Pn))
assert(degree J== d^2-sum(L,r->r^2))
betti(fJ=res J)
betti(D=(transpose fJ.dd_4)**Pn^{-n})

z = symbol z
adj=adjointMatrix(D,z)
elapsedTime (numList,adjList,I)=adjunctionProcess(J,true);

/// 

TEST ///

kk=ZZ/nextPrime(10^3)
P2=kk[t_0..t_2]
d=7
L=toList(6:2)|toList(10:1)
n=expectedDimension(d,L)-1
x=symbol x
Pn=kk[x_0..x_n]
betti(J=rationalSurface(P2,d,L,Pn))
assert(degree J== d^2-sum(L,r->r^2))
betti(fJ=res J)
c=length fJ
betti(D=(transpose fJ.dd_c)**Pn^{-n})
z=symbol z
adjointMatrix(D,z)
elapsedTime (numList,adjList,ptsList,I)=adjunctionProcess(J,1);
numList
minimalBetti I
///



TEST ///
kk=ZZ/nextPrime(10^3)
P2=kk[t_0..t_2]
d=7
L=toList(6:2)|toList(10:1)
n=expectedDimension(d,L)-1
x=symbol x
Pn=kk[x_0..x_n]
betti(J=rationalSurface(P2,d,L,Pn))
assert(degree J== d^2-sum(L,r->r^2))
elapsedTime (numList,adjList,ptsList,I)=adjunctionProcess J;
betti(H=parametrization(P2,adjList))
assert(sub(J,H)==0)
phi=map(P2,ring J,H);
assert(ker phi==J)

///


TEST ///
kk=ZZ/nextPrime(10^3)
P2=kk[t_0..t_2]
d=7
L={3}|toList(6:2)|toList(6:1)
expectedDimension(d,L)
P5=kk[x_0..x_5]
J=rationalSurface(P2,d,L,P5);
minimalBetti J
elapsedTime (numList,adjList,ptsList,I)=adjunctionProcess J;
numList
minimalBetti I
k=2
(A,B,eq)=extension(J,k);
assert(eq==0)
A*B==0
betti (fA=res coker transpose A)
I=ideal fA.dd_k;
assert(degree I== degree J and codim I== codim J)
dim I
minimalBetti I
/// 

TEST///
kk=ZZ/nextPrime(10^3);
P3=kk[x_0..x_3]
I=ideal random(P3^1,P3^{4:-2})
P5=kk[z_0..z_5]
betti(J=reyeCongruence(I,P5))
minimalBetti J
(numList,adjList,ptsList,E)=adjunctionProcess(J,1);
numList
minimalBetti E
(A,B,eq)=extension(E,2);
assert(eq==0)
P9 = ring A
assert(dim P9 == 10)
betti(Y=ideal syz transpose A)
betti (fY= res Y)
dim Y
///


TEST///
kk=ZZ/nextPrime 10^9
Y=maximalExtensionOfReyeFanoModel(kk,symbol z);
betti(fY=res Y)
dim Y,degree Y 
P9=ring Y      	
adj=adjointMatrix(fY.dd_3,symbol x)
q=ann coker adj
Sq=ring q/q
betti(m10x10=syz transpose(adj**Sq))
assert(rank m10x10==3 and dim minors(2,m10x10)==0)
E=ideal(gens Y%ideal random(P9^1,P9^{4:-1}));
P6=kk[support E]
E=sub(E,P6);
dim E
(numList,adjList,ptList,I)=adjunctionProcess(E,1);
numList
P6a=ring I
--minimalBetti I
I1=sub(I,P6a);
minimalBetti I1
///

 
----------------- end Tests ------------------------
-----------------------------------------

beginDocumentation()

document { 
  Key => "SurfacesAndExtensions",
  Headline => "Rational surfaces and extensions",
   
   PARA{},"The main functions concerning surfaces are:",
   UL{   TO  "linearSystemOnRationalSurface",
         TO  "rationalSurface",
	 TO  "expectedDimension",
	 TO  "adjointMatrix",
	 TO  "slowAdjunctionCalculation",
	 TO  "adjunctionProcess",
	 TO  "parametrization",
	 TO  "threeRegularSurfaceOfCodim3", 
	 TO  "reyeCongruence",
	 TO  "fanoPolarizedEnriquesSurface",
	 TO  "analyseFanoPolarizedEnriquesSurface",
	 TO  "specialFamiliesOfSommeseVandeVen"  
      },
  PARA{},"The main functions concerning extensions are:",
   UL{   TO  "extension",
         TO  "maximalExtensionOfReyeFanoModel",
	 TO  "listOfN33Surfaces",
	 TO  "extensionsOfAGeneralParacanonicalCurve",
	 TO  "extensionsOfAGeneralPrymCanonicalCurve",
	 TO  "prymCanonicalEmbeddedPlaneQuintic",
	 TO  "paracanonicalEmbeddedPlaneQuintic",
	 TO  "identifyMaximalExtension",
	 TO  "extensionsOfSpecialCurves",
	 TO  "extensionsOfNodalPrymCurve"
      },           
   

   PARA{}, "This package has two themes. The first topic are functions to create rational and Enriques surfaces and to
   study them via the adjunction process.",
   
   PARA{},"The second topic are extension of varieties X in P^n to varieties Y in P^(n+e). 
   If the free resolution of  the ideal I_X has two consequtive linear maps 
   then a maximal extension can be computed using the function extension. 
   If the returned ideal eq
   is zero, then one has immediately the maximal extension. In general maximal extension 
   correspond to maximal linear
   subspaces of of the vanishing loci V(eq).",
   
   PARA{},"A case where eq=0 is the case of a 3-regular surface X of degree 10 in P5. These surfaces 
   have been classified by Truong [Tru].
   They differ by the self-intersection number of the canonical divisor of X. All of them have 
   the same Betti table. They satisfy the condition N_{3,3} of [AHK]. Several of the functions in the package
   are needed in the proofs of the main results of [ST].
   ",
   
   PARA{},"References:",
   PARA{},"[AHK] J. Ahn, K. Han, and S. Kwak. On the first nontrivial strand of syzygies of projective schemes and condition ND(l), Algebra Number Theory 17 (2023), no. 8, 1359–1380.",
   PARA{},"[BKR] G. Brown, M. Kerber, and M. Reid. Fano 3-folds in codimension 4, Tom and Jerry. I, Compos. Math. 148 (2012), no. 4, 1171–1194.",
   PARA{},"[CD] F. R. Cossec and I. V. Dolgachev, Enriques surfaces. I, Prog. Math., vol. 76, Boston, MA etc.: Birkha ̈user Verlag, 1989.",
   PARA{},"[DK] I. Dolgachev and S. Kondo. Enriques surfaces II, 2023.",
   PARA{},"[CM] A. Conte and J. P. Murre, Algebraic varieties of dimension three whose hyperplane sections are Enriques surfaces, Ann. Sc. Norm. Super. Pisa, Cl. Sci., IV. Ser. 12 (1985), 43–80.", 
   PARA{},"[DES] W. Decker, L. Ein, F.-O. Schreyer. Construction of surfaces in P4. J. Alg. Geom. 2 (1993), 185-237.",
   PARA{},"[ESB] L. Ein, N. Shepherd-Barron, Some special Cremona transformations, Am. J. Math. 111 (1989), no. 5, 783–800.",
   PARA{},"[FKO] G. Fløystad, J. Kileel, and G. Ottaviani, The Chow form of the essential variety in computer vision, J. Symb. Comput. 86 (2018), 97–119.", 
   PARA{},"[Pin] H. C. Pinkham, Deformations of algebraic varieties with Gm action, Asterisque, vol. 20, Soci ́et ́e Math ́ematique de France (SMF), Paris, 1974.",
   PARA{},"[ST] F.-O. Schreyer, H.L. Truong. Extensions and paracanonical curves of genus 6, arXiv .",
   PARA{},"[SVdV] A. Sommese, A. Van de Ven. On the adjunction mapping, Math. Ann. 278 (1987), 593–603.",
   PARA{},"[Tru] H.L Truong. Classification and geometric properties of surfaces with property N_{3,3}. J. Pure Appl. Algebra 227, No. 7, Article ID 107325, 24 p. (2023)."
  
   }



doc ///
  Key
    linearSystemOnRationalSurface
    (linearSystemOnRationalSurface,Ring,ZZ,List)
    (linearSystemOnRationalSurface,List,ZZ,List)
  Headline
    compute a linear system on a rational surface
  Usage
     H=linearSystemOnRationalSurface(P2,d,L)
     H=linearSystemOnRationalSurface(points,d,L)
  Inputs 
    P2: Ring
          homogeneous coordinate ring of P2
    points: List
         a list of ideals defining points in P2
    d: ZZ
          degree of the desired forms
    L: List
          {r_1,...,r_s} of multiplicities 
  Outputs
     H: Matrix
        a 1xn matrix whose entreis are a bases of L(d;r_1p_1,...,r_sp_s)      
  Description
     Text
       The function chooses randomly s point p_i in P2 and computes the 
       linear system of form of degree d which have multiplicity r_i at the point p_i       
     Example
        kk=ZZ/nextPrime(10^3)
	t=symbol t
	P2=kk[t_0..t_2]
	d=8
	L=toList(3:3)|toList(2:4)|{1}
        expectedDimension(d,L)	 
        betti(H=linearSystemOnRationalSurface(P2,d,L))	
///
 

doc ///
  Key
    expectedDimension
    (expectedDimension,ZZ,List)
  Headline
    compute the expected dimension of a linear system on a rational surface
  Usage
     expectedDimension(d,L)
  Inputs 
    d: ZZ
          degree of the desired forms
    L: List
          {r_1,...,r_s} of multiplicities 
  Outputs
     : ZZ
       the expected dimension of L(d;r_1p_1,...,r_sp_s)     
  Description
     Text
       computes the expected dimension
       max(0,binomial(d+2,2)-sum binomial(r_i+1,2))
       of a linear system with assigned base points on P2
     Example
	d=8
	L=toList(3:3)|toList(2:4)|{1}
        expectedDimension(d,L)
	kk=ZZ/nextPrime(10^3)
	t=symbol t
	P2=kk[t_0..t_2]	 
        betti(H=linearSystemOnRationalSurface(P2,d,L))	
///	 
      

doc ///
  Key
    rationalSurface
    (rationalSurface,Ring,ZZ,List,Ring)
    (rationalSurface,Ring,ZZ,List,Symbol)
    (rationalSurface,List,ZZ,List,Symbol)
  Headline
    compute the ideal I of the rational surface      
  Usage
    I=rationalSurface(P2,d,L,Pn)
    I=rationalSurface(P2,d,L,x)
    I=rationalSurface(points,d,L,x)
  Inputs 
    P2: Ring
         homogeneous coordinate ring of P2,
    points: List
        list of ideals of points in P2
    d: ZZ
         degree of the desired forms
    L: List
          {r_1,...,r_s} of multiplicities
    Pn: Ring
       coordinate ring of Pn
    x: Symbol
        variable name 
  Outputs
     I: Ideal
       of a rational surface 
  Description
     Text
       The function chooses randomly s point p_i in P2 and computes the 
       linear system H=L(d;L) of form of degree d which have multiplicity r_i at 
       the point p_i. 
       
       Then the ideal of the image of P2 of under the rational map
       defined by the linear system H is computed.    
     Example
	d=6
	L=toList(6:2)|toList(2:1)
        n=expectedDimension(d,L)-1
	kk=ZZ/nextPrime(10^3)
	t=symbol t
	P2=kk[t_0..t_2]	 
        y=symbol y
	betti(I=rationalSurface(P2,d,L,y))
	x = symbol x
	Pn=kk[x_0..x_n]
	betti(I=rationalSurface(P2,d,L,Pn))
	degree I, genus I, dim I
	minimalBetti I
	d^2-sum(L,r->r^2)== degree I
	(numList,adjList,ptsList,J)=adjunctionProcess(I);
	numList
	minimalBetti J
///	 

doc ///
  Key
    adjointMatrix
    (adjointMatrix,Matrix,Symbol)
  Headline
    compute the adjoint matrix
  Usage
     adj=adjointMatrix(D,z)
  Inputs 
    D: Matrix
           the transpose of a linear presentation matrix of omega_X(1)
  Outputs
    adj: Matrix
       the presentation matrix of O_X(1)     
  Description
     Text
        compute the presentation matrix of the line bundle O_X(1)
	as a module on the adjoint variety
     Example
	d=7
	L=toList(7:2)|toList(8:1)
        n=expectedDimension(d,L)-1
	kk=ZZ/nextPrime(10^3)
	t=symbol t, x= symbol x
	P2=kk[t_0..t_2]
	Pn=kk[x_0..x_n]	 
        betti(I=rationalSurface(P2,d,L,Pn))
	c=codim I
	elapsedTime fI=res I
        betti(omega=presentation coker transpose fI.dd_c**Pn^{-n-1})
	D=transpose omega;
	z= symbol z
	betti(adj=adjointMatrix(D,z))
	support adj
    	minimalBetti ann coker adj
	(numList,adjList,ptsList,J)=adjunctionProcess(I,1);
	numList
	betti(adjList_0)
	minimalBetti J		
///	 

doc ///
  Key
    slowAdjunctionCalculation
    (slowAdjunctionCalculation,Ideal,Matrix,Symbol)
  Headline
    compute the adjoint variety and the presentation of O(1)
  Usage
     (I1,adj)=slowAdjunctionCalculation(I,D,z)
  Inputs
    I: Ideal
    	of a smooth projective surface X
    D: Matrix
           the transpose of a linear presentation matrix of omega_X(1)
    z: Symbol
    	variable name
    
  Outputs
    I1 : Ideal
    	of the adjoint surface in a Pn
    adj: Matrix
       the presentation matrix of O_X(1) as O_Pn-module    
  Description
     Text
        compute the ideal of the adjoint variety and the presentation matrix of the line bundle O_X(1)
	as a module on the adjoint variety
     Example
        kk=ZZ/101
	P2=kk[x_0..x_2]
	betti(Y=rationalSurface(P2,8,toList(4:3)|toList(4:2)|{1,1},symbol z))
	P6=ring Y, dim P6==7
	betti(fY=res Y)
	betti(omegaY=coker transpose fY.dd_4**P6^{-dim P6})
	betti(D=transpose presentation omegaY)
	(I,adj)=slowAdjunctionCalculation(Y,D,symbol x);
	betti adj
	P4=ring I, dim P4==5
	PI=P4/I
	m=adj**PI;
	betti(sm=syz transpose m)
	rank sm==1
	(numList,adjList,ptsList,I)=adjunctionProcess Y;
	numList, minimalBetti I
///


doc ///
  Key
    adjunctionProcess
    (adjunctionProcess,Ideal)
    (adjunctionProcess,Ideal,ZZ)
  Headline
    perform the adjunction process
  Usage
     (numList,adjList,ptsList,J)=adjointMatrix(I)
     (numList,adjList,ptsList,J)=adjointMatrix(I,N)
  Inputs 
    I: Ideal
           of a projective surface
    N: ZZ
        number of adjunction steps
  Outputs
    numList: List
       numerical Data of the adjunction process
    adjList: List
       list of adjoint matrices
    ptsList: List
       list of ideal if the exceptional points
    J: Ideal
        ideal of the final surface in the adjunction process       
  Description
     Text
        Adjunction determines the image X' of X under the morphism phi: X -> X'
	defined by |H+K|. By Sommese and Van de Ven [SVdV]
	|H+K| is birational and blows down presisely all (-1) lines of unless
	
	(1) X is a P2 linearly or quadratically embedded, or ruled in lines,
	
	(2) X is a anticanonical embedded Del Pezzo surface,
	
	(3) X is a conic bundle in which case phi_{|H+K|}: X -> B
	maps X to a curve B and the fibers are conics, or
	
	(4) X is an element of one of the four families of exceptions where |K+H|
	defines a finite to 1 map. See TO "specialFamiliesOfSommeseVandeVen".
	
	Since a (-1) conic on X become (-1) line on X', repeating this process finally reaches 
	a minimal surface unless X has negative Kodaira dimension.
	
	In case X is a rational surface, and the lucky case that the
	final surface is P2, one can use the list adjList to get a rational 
	parametrization.
	
	In case one ends up with a del Pezzo suface or a conic bunlde, one has to identify the 
	exceptional lines, thus one might need an algebraic field extension, 
	to get a rational parametrization. However, one can always parametrize X in terms of the final
	surface in the adjunction process.
	
	The nummerical data are collected in a list with an entry 
	
	(n,d,pi)= (dim Pn_i, degree X_i, sectional genus of X_i)
	
	for each surface X_i in the adjunction process, starting with X=X_0
	and an entry the integer k if X_i -> X_(i+1) blows down k (-1) lines.	
     Example
	d=7
	L=toList(7:2)|toList(8:1)
        n=expectedDimension(d,L)-1
	kk=ZZ/nextPrime(10^3)
	t=symbol t, x= symbol x
	P2=kk[t_0..t_2]
	Pn=kk[x_0..x_n]	 
        betti(I=rationalSurface(P2,d,L,Pn))
	minimalBetti I	
	(numList,adjList,ptsList,J)=adjunctionProcess(I);
	numList
	P2=ring J
	betti(H=parametrization(P2,adjList))
    	elapsedTime sub(I,H)
	phi=map(P2,Pn,H);
	elapsedTime betti(I'=trim ker phi)
	I'== I
        elapsedTime basePts=primaryDecomposition ideal H;
	tally apply(basePts,c->(dim c, degree c, betti c))  		
///	 


doc ///
  Key
    parametrization
    (parametrization,Ring,List)
  Headline
    compute a rational parametrization
  Usage
     H=parametrization(PJ,adjList)
  Inputs
    PJ: Ring
           coordinate ring of the last adjoint surface
    adjList: List
        list of adjoint matrices
  Outputs
    H: Matrix
       parametrization of the rational surface X      
  Description
     Text
        Let adjList be the list of adjoint matrices comming out of the adjunction
	process of a rational surface X. If the final surface is a P2 then
	the function computes the rational parametrization of X. In other cases the 
	function returns rational parametrization from the final surface X'' in the adjunction
	process.
		
     Example
	d=7
	L=toList(7:2)|toList(8:1)
        n=expectedDimension(d,L)-1
	kk=ZZ/nextPrime(10^3)
	t=symbol t, x= symbol x
	P2=kk[t_0..t_2]
	Pn=kk[x_0..x_n]	 
        betti(I=rationalSurface(P2,d,L,Pn))
	minimalBetti I	
	(numList,adjList,ptsList,J)=adjunctionProcess(I);
	numList
	P2=ring J
	betti(H=parametrization(P2,adjList))
    	elapsedTime sub(I,H)
	phi=map(P2,Pn,H);
	elapsedTime betti(I'=trim ker phi)
	I'== I
        elapsedTime basePts=primaryDecomposition ideal H;
	tally apply(basePts,c->(dim c, degree c, betti c))		
///

doc ///
  Key
    extension
    (extension,Ideal,ZZ)
  Headline
    compute the extension of I to a larger Pn
  Usage
     (A,B,eq)=extension(I,k)
  Inputs 
    I: Ideal
          homogeneous ideal of a projective variety X
    k: ZZ
         position where the minimal free resolution has two consecutive
	 linear syzyzgy matrices       
  Outputs
    A: Matrix
    B: Matrix
       first order extension matrices
    eq: Ideal
      ideal of obstructions     
  Description
     Text
        Suppose the minimal free resolution fI has two linear differentials
	phi=fI.dd_k and psi=fI.dd_(k+1) with k < codim I.
	The function computes the maximal linear matrices A,B such that
	    
	    A*psi+phi*B=0
	
 	(One can view this as a linear system of equations for unknown entries of
	A and B.)
	Then A and B define maximal first order extensions and
	the entries of A*B generate an ideal eq. Then maximal linear subspaces of 
        the vanishing loci V(eq) coorespond to maximal extension.
	
	In suprisingly many cases, we have that eq is the zero ideal,
	so that A and B define two differentials of the minimal free resolution
	of a maximal extension of X. 
     Example
	kk=ZZ/nextPrime(10^3)
	P5=kk[x_0..x_5]
	d=9
	L=toList(6:3)|toList(4:2)|toList(1:1)
	P2=kk[t_0..t_2]
	I=rationalSurface(P2,d,L,P5);
	minimalBetti I
	(A,B,eq)=extension(I,2);
	eq==0
	n=dim ring B-1
	Pn=kk[y_0..y_n]	
	betti(B1=sub(B,vars Pn))
	betti(fB=res coker transpose B1)
	X=ideal fB.dd_3;
	genera X
     Text
        Pinkhams example [Pin]: The rational normal curve of degree 4 in P4 extends in two different
	ways: into P1xP3 in P7 or to the Veronese surface v_2(P2) in P5.
     Example
        kk=QQ
        P4=kk[x_0..x_4] 
	m2x4=matrix apply(2,i-> apply(4,j-> x_(i+j)))
	I=minors(2,m2x4)
	minimalBetti I
	(A,B,eq)=extension(I,2); 
	eq
	ceq=decompose eq
	Is=apply(ceq,c->(B1=B%c;
		P=kk[support B1];
		fB1=res coker transpose sub(B1,P);
		ideal fB1.dd_3)) 
        apply(Is,I->dim I)
	(numList,adjList,ptsList,J)=adjunctionProcess(Is_1);
	dim J,degree J, J
	h=parametrization(ring J,adjList)
	sub(Is_1,h)
        phi=map(ring h, ring Is_1,h)
	ker phi== Is_1
	-- Is_1 describes the Veronese surface
	betti(fI0=res (Is_0))
	z=symbol z
	adj=adjointMatrix(fI0.dd_3,z)
	q=ann coker adj
	Sq=ring q/q
    	betti (sadjt=syz transpose (adj**Sq))
        rank sadjt==4 and dim minors(3,sadjt)==0
	-- =>  V(Is_0) is a P3-bundle over the conic V(q)
     Text
       Tom and Jerry [BKR]: The Del Pezzo surface of degree 6 extends in 
       two ways. The maximal extensions are P2xP2 in P8 and P1xP1xP1 in P7. 
     Example
       kk=QQ
       P2=kk[t_0..t_2] 
       h=gens trim ideal (basis(3,P2)%ideal apply(gens P2,i->i^3))      
       P6=kk[x_0..x_6]
       betti(I=trim ker map(P2,P6,h))
       degree I	
       minimalBetti I
       (A,B,eq)=extension(I,2);
       betti eq
       ceq=decompose eq
       Is=apply(ceq,c->(A1=A%c;
		P=kk[support A1];
		ideal syz transpose sub(A1,P)));
       apply(Is,I-> (dim ring I,dim I))     
///	 

doc ///
  Key
    threeRegularSurfaceOfCodim3
    (threeRegularSurfaceOfCodim3,ZZ,Ring)
  Headline
    create the ideal of a 3-regular surface X of codim three
  Usage
     I=threeRegularSurfaceOfCodim3(kSquare,kk)
  Inputs
    kSquare: ZZ
          the self-intersection number of the canonical divisor K_X
    kk: Ring
        the ground field
  Outputs
    I: Ideal
       of a surface      
  Description
     Text
        The 3-regular surfaces of degree 10 in P5 are classified by 
	K^2_X in {-6,\ldots,0}. The function creates an example for the given kSquare.	
     Example
        kk=ZZ/nextPrime(10^3)
	I=threeRegularSurfaceOfCodim3(-5,kk);
        minimalBetti I
	netList apply(toList(-6..0),kSquare-> (
		I=threeRegularSurfaceOfCodim3(kSquare,kk);
	        (numList,adjList,ptsList,J)=adjunctionProcess(I,1);
		(A,B,eq)=extension(I,2);
		assert(eq==0);
	        (kSquare, eq==0, numList_1, minimalBetti J,numList_2_1, dim ring B-1)
		))
	P3=kk[x_0..x_3];
	betti(web=ideal random(P3^1,P3^{4:-2}))
	P5=kk[y_0..y_5];
	Y1=reyeCongruence(web,P5);
	minimalBetti Y1
	(numList,adjList,ptsList,I)=adjunctionProcess(Y1,1);
	minimalBetti I
	(numList,adjList,ptsList,J)=adjunctionProcess(I,1);
	(A,B,eq)=extension(I,2);
	netList {(0, eq==0, numList_1, minimalBetti J,numList_2_1, dim ring B-1)}
///

doc ///
  Key
    reyeCongruence
    (reyeCongruence,Ideal,Ring)
  Headline
    compute the Reye congruence of a web of quadrics
  Usage
     I=reyeCongruence(J,P5)
  Inputs
    J: Ideal
          web of quadrices in P3
    P5: Ring
        coordinate ring of P5
  Outputs
    I: Ideal
       of a surface, the corresponding Reye congruence      
  Description
     Text
        Reye has associated to a web quadrics in P3 the congruence contained in the Plucker quadric of those
	lines L in P3 which are contained in a pencil of quadrics. This is a famous example of a nodal Enriques surface
	c.f. [CD], [DK].
       
     Example   
        kk=ZZ/nextPrime(10^3)
	x=symbol x
	P5=kk[x_0..x_5]
	P3=kk[y_0..y_3]
	betti(J=ideal random(P3^1,P3^{4:-2}))
	I=reyeCongruence(J,P5);
	minimalBetti I
	I_0 -- the plucker quadric
	(numList,adjList,ptsList,I1)=adjunctionProcess(I,1);
	numList
	minimalBetti I1	
///
///
betti jacobian I1
codim I1
elapsedTime betti(singI1=trim(I1+minors(3,jacobian I1)))  -- 113.584 seconds elapsed
dim singI1
elapsedTime betti(singI=trim(I+minors(3,jacobian I)))  --
dim singI
P5=ring I1
C=ideal(gens I1%ideal random(1,P5));
P4=kk[support C]
C=sub(C,P4);
(A,B,eq)=extension(C,2);
betti eq

///

doc ///
  Key
    maximalExtensionOfReyeFanoModel
    (maximalExtensionOfReyeFanoModel,Ring,Symbol)
  Headline
    direct construction of the maximal extension of the Reye Fano model
  Usage
     X=maximalExtensionOfReyeFanoModel(kk,z)
  Inputs
    kk: Ring
          the ground field
    z: Symbol
        name for the homogeneous coordinates of a P9
  Outputs
    X: Ideal
       of a codimension three 3-regular variety     
  Description
     Text
        The  Fano model of a Reye congruence extends maximally to a P9.
	This code constructs the maximal extension directly. Its zero loci is
	isomorphic to a P2-bundle over the Plucker quadric in P5. Hence 
	X defines a 6-fold. 
	It is well known that a hyperplane section is the
	essential vision variety, see [FKO].
	The dimension 3 linear section are the famous Enriques-Nikulin 3-folds.
	see [CM].	
     Example   
        kk=ZZ/nextPrime(10^3)
	X=maximalExtensionOfReyeFanoModel(kk,symbol z)
	minimalBetti X	
///	
///

kk=QQ
X=maximalExtensionOfReyeFanoModel(kk,symbol z)
minimalBetti X
elapsedTime betti(singX=trim(X+minors(3,jacobian X)))
codim singX, degree singX
betti(sings=saturate(singX))
elapsedTime betti(singXr=radical singX)
minimalBetti singXr
P9=ring X
P3=kk[x_0..x_3]
h=(basis(2,P3))_{0,1,4,2,5,7,3,6,9,8}
D=diagonalMatrix({1,1,-1,1,1,-1,1,1,-1,1})
phi=map(P3,P9,h*D)
J=ker phi
singXr==J
dim X
P3y=kk[y_0..y_3]
hy=sub(h*D,vars P3y)
hx=sub(hy, vars P3)
P3xP3=P3**P3y
hxhy=sub(hx,P3xP3)+sub(hy,P3xP3)
betti(secV2P3=ker map(P3xP3,P9,hxhy))
secV2P3==X

///

doc ///
  Key
    tangentCone1   
    (tangentCone1,Matrix,Ideal)
  Headline
    compute the tangent cone of a variety at a point
  Usage
     cpX=tangentCone1(pt,I)
  Inputs
    pt: Matrix
          the coordinates of a point in P^n
    I: Ideal
        homogeneous ideal of a subscheme X of P^n
  Outputs
    cpX: Ideal
       the ideal of the tangent cone of X at pt   
  Description
     Text
        Extends the functionality of the function tangentCone
	to compute the tangent cone at a given point.
	Notice that the result is in different coordinate then the original
     Example   
        kk=ZZ/nextPrime(10^3)
	P3=kk[x_0..x_3]
	Ia=ideal(x_0*x_1-x_2^3)
	X=homogenize(Ia,x_3)
	pt=matrix{{0,0,0,1}}
	cpX=tangentCone1(pt,X)
///	

doc ///
  Key
    fanoPolarizedEnriquesSurface   
    (fanoPolarizedEnriquesSurface,Ring,Symbol)
  Headline
    construct a Fano polarized Enriques surface together with a point
  Usage
     (J,pt)=fanoPolarizedEnriquesSurface(kk,z)
  Inputs
    kk: Ring
          the ground field
    z: Symbol
        name for the homogeneous coordinates of a P5
  Outputs
    J: Ideal
       the ideal of an Enriques surface E
    pt: Ideal
       ideal of a point on E  
  Description
     Text
        By [DES] the universal family of Fano polarized Enriques surface
	is birational to the moduli space of genus 5 curves.
	The code picks a random complete intersection of three quadrics in P4, 
	considers its the apolar ideal which defines a finite length module M
	with Hilbert function (1,5,3), and conputes the blown-up Enriques surface S in P4
	with H^1_*(P4,I_S) = M(-2). In a second step the function computes the first adjoint
	surface E in the adjunction process, and the image pt of the exceptional line of S on E.
     Example   
        kk=ZZ/nextPrime(10^3)
	(J,pt)=fanoPolarizedEnriquesSurface(kk,symbol z);
	minimalBetti J
    	betti pt
	dim pt==1 and degree pt == 1
	pt==pt+J
///	



doc ///
  Key
    specialFamiliesOfSommeseVandeVen   
    (specialFamiliesOfSommeseVandeVen,Ring,ZZ)
  Headline
    produce a member of the special family
  Usage
     Y=specialFamiliesOfSommeseVandeVen(kk,fam)
  Inputs
    kk: Ring
          the ground field
    fam: ZZ
        number of the family
  Outputs
    Y: Ideal
       the ideal of a surface   
  Description
     Text
        By [SVdV] four families of smooth surfaces Y behave differently
	in the adjunction process: |H+K_Y| defines a morphism Y -> Y_1
	which is generically finite to 1 instead of birational.
	These families are
	
	1) P2(6;2p_1,...,2p_7)
    
    	2) P2(6;2p_1,...,2p_7,p_8)
    
    	3) P2(9;3p_1,...,3p_8)
    
    	4) Y=P(E) where E is a indecomposabe rank 2 vector bundle over an elliptic curve
    	    and H=3B, where B in Y is the section with B^2=1.

     Example   
        kk=ZZ/nextPrime(10^3)	
	Y=specialFamiliesOfSommeseVandeVen(kk,1);
	betti(fY= res Y)
	betti (fib=trim(ideal(fY.dd_4*random(kk^3,kk^1))))
	dim fib, degree fib
     Text 
        The adjunction map |H+K_Y|: Y -> P2
	is 2:1 in case of family 1.
     Example   	
	Y=specialFamiliesOfSommeseVandeVen(kk,2);
	betti(fY= res Y)
	betti (fib=trim(ideal(fY.dd_3*random(kk^3,kk^1))))
	dim fib, degree fib
     Text 
        The adjunction map |H+K_Y|: Y -> P2
	is 2:1 in case of family 2.
     Example
        Y=specialFamiliesOfSommeseVandeVen(kk,3);
     	betti(fY=res Y)
     	P6=ring Y,dim P6==7
	(Q,adj)=slowAdjunctionCalculation(Y,fY.dd_4,symbol u);
    	dim Q, degree Q
     	P3=ring Q; dim P3==4
     	while (L=ideal random(P3^1,P3^{2:-1});
    	    pts=decompose (L+Q);
    	    #pts<2) do ()
     	pt=sub(syz transpose jacobian first pts,kk)
     	betti(fib= trim ideal(fY.dd_4*pt))
     	dim fib, degree fib
     Text 
        The adjunction map |H+K_Y|: Y -> Q 
	is 2:1 onto a quadric in P3 in case of family 3.
     Example
        Y=specialFamiliesOfSommeseVandeVen(kk,4);
	betti(fY=res Y)
	P5=ring Y, dim P5==6
	betti(omegaY=Ext^2(module Y,P5^{-6}))
	betti(fib=trim ideal (random(kk^1,kk^3)*presentation omegaY))
	dim fib, degree fib
     Text 
        The adjunction map |H+K_Y|: Y -> P2 
	is 3:1 in case of family 4.         
///	




doc ///
  Key
    listOfN33Surfaces   
    (listOfN33Surfaces,Ring)
  Headline
    list randomly choosen N33 surfaces
  Usage
     L=listOfN33Surfaces(kk)
  Inputs
    kk: Ring
          the ground field
  Outputs
    L: List
       with entries pairs (kSquare,I) of class (ZZ,Ideal)
  Description
     Text
        A N33 surface Y in P5 satisfies K^2 in {-6,...,0}.
        For each K^2 they form a single family. Those with K^2<0 are rational.
	The one with K^2=0 are Enriques surfaces. The function produces a list of randomly 
	choosen elements in each family.
     Example   
        kk=ZZ/nextPrime(10^3)
	L=listOfN33Surfaces(kk);
	netList apply(L,(k2,Y)->(
		(A,B,eq)=extension(Y,2);
		(numList,adjList,ptsList,I)=adjunctionProcess(Y,1);
		(k2,eq==0,dim ring A-dim ring Y, numList_1, minimalBetti I)))
	L1=apply(drop(L,-1),(k2,Y)->(
		(numList,adjList,ptsList,I)=adjunctionProcess(Y);
		(k2,numList, minimalBetti I)));
	(numList,adjList,ptsList,I)=adjunctionProcess((last L)_1,2);
	netList (append(L1,(0,numList,minimalBetti I)))
///

doc ///
  Key
    extensionsOfAGeneralParacanonicalCurve   
    (extensionsOfAGeneralParacanonicalCurve,String)
  Headline
    print code which computes the maximal extensions of a general paracanonical curve of genus 6 
  Usage
     extensionsOfAGeneralParacanonicalCurve(S)
  Inputs
    S: String
          a string to set the random seed
  Outputs
     : String
       code which verifies Theorem 3.2 of [ST]
  Description
     Text
        Prints the code whose excecution is needed to prove Theorem 3.2 of [ST]
	which in summary says that a general paracanonical curve of genus 6 has
	26 families of 1-extensions to surfaces Y
     Example   
        S="find an example which decomposes enough"
	extensionsOfAGeneralParacanonicalCurve(S)
///

doc ///
  Key
    extensionsOfAGeneralPrymCanonicalCurve   
    (extensionsOfAGeneralPrymCanonicalCurve,String)
  Headline
    print code which computes the maximal extensions of a general Prym canonical curve of genus 6 
  Usage
     extensionsOfAGeneralPrymCanonicalCurve(S)
  Inputs
    S: String
          a string to set the random seed
  Outputs
     : String
       code which verifies the Theorem 3.3 of [ST]
  Description
     Text
        Prints the code whose excecution is needed to prove Theorem 3.3 of [ST]
	which in summary says that a general Prym canonical curve C has 27
	families of 1-extensions to surfaces Y.
     Example   
        S="An example which decomposes enough over the given field"
	extensionsOfAGeneralPrymCanonicalCurve(S)
///

doc ///
  Key
    extensionsOfNodalPrymCurve   
    (extensionsOfNodalPrymCurve,String)
  Headline
   print code which computes the maximal extensions of a nodal Prym curve C
  Usage
     extensionsOfNodalPrymCurve(S)
  Inputs
    S: String
          a string to set the random seed
  Outputs
     : String
       code which verifies the Theorem 6.4 of [ST]
  Description
     Text
     	Let C be the hyperplane section of a Fano polarized nodal Enriques surface.
	This command prints the code whose excecution is needed to prove Theorem 4.6 of [ST]
	which in summary says that a general such C has 7 families of 1-extensions.
     Example   
        S="example which decompose over the given suffiently enough"
	extensionsOfNodalPrymCurve(S)
///

doc ///
  Key
    prymCanonicalEmbeddedPlaneQuintic   
    (prymCanonicalEmbeddedPlaneQuintic,Ring)
  Headline
    compute a Prym canonical embedded plane quintic
  Usage
     I=prymCanonicalEmbeddedQuintic(kk)
  Inputs
    kk: Ring
       the ground field
  Outputs
    I : Ideal
       ideal of Prym canonical embedded quintic
  Description
     Text
        Using a symmetric 5x5 matrix of linear forms we compute the corresponding
	Prym canonical embedded curve in P4
     Example   
	kk=ZZ/nextPrime 10^3
	betti(I=prymCanonicalEmbeddedPlaneQuintic kk)
	minimalBetti I
	(A,B,eq) = extension(I,2);
	betti eq
	ceq =decompose eq;
	apply(ceq,c->betti c)
	Zs=apply(ceq,c->(Z=ideal syz transpose (A%c);P=kk[support Z];sub(Z,P)));
	apply(Zs, Z -> dim ring Z)
	Ys=apply(Zs,Z->(P=ring Z;L=ideal random(P^1,P^{dim P-6:-1});
		Y=ideal(gens Z%L);P5=kk[support Y];sub(Y,P5)));
    	tally apply(Ys,Y-> minimalBetti Y)
	netList apply(Ys,Y->((numList,adjList,ptsList,I)=adjunctionProcess(Y,1);
	    (numList,minimalBetti I)))
 ///


doc ///
  Key
    paracanonicalEmbeddedPlaneQuintic   
    (paracanonicalEmbeddedPlaneQuintic,Ring)
  Headline
    compute a paracanonical embedded plane quintic
  Usage
     I=paracanonicalEmbeddedQuintic(kk)
  Inputs
    kk: Ring
       the ground field
  Outputs
    I: Ideal
       ideal of paracanonical embedded quintic
  Description
     Text
        Using a 5x5 matrix of linear forms we compute the corresponding
	a paracanonical embeddeding into P4 of the corresponing determinantal plane quintic
     Example   
	kk=ZZ/nextPrime 10^3
	betti(I=paracanonicalEmbeddedPlaneQuintic(kk))
	minimalBetti I
	(A,B,eq) = extension(I,2);
	betti eq
	eq==0
	Z=ideal syz transpose A;
	P14=ring Z; dim P14==15 
	L=ideal random(P14^1,P14^{15-6:-1});
	Y=ideal(gens Z%L);P5=kk[support Y];
	Y=sub(Y,P5);
    	(numList,adjList,ptsList,I)=adjunctionProcess(Y,1);
	numList,minimalBetti I
 ///

doc ///
  Key
    analyseFanoPolarizedEnriquesSurface   
    (analyseFanoPolarizedEnriquesSurface,Ideal)
  Headline
    print code which analyses a Fano polarized Enriques surface
  Usage
     S=analyseFanoPolarizedEnriquesSurface(Y)
  Inputs
    Y: Ideal
       of a Fano polarized Enriques surface in P5
  Outputs
     S: String
  Description
     Text
        Prints commands which compute the half pencils,
	the correponding pencils,
	the base loci and intersection numbers.	
     Example   
	kk=ZZ/19
	Z=maximalExtensionOfReyeFanoModel(kk,symbol z);
	P9=ring Z;
	Y=ideal(gens Z%ideal random(P9^1,P9^{4:-1}));
	P5=kk[support Y]
	Y=sub(Y,P5);
        analyseFanoPolarizedEnriquesSurface(Y)
 ///


doc ///
  Key
    identifyMaximalExtension   
    (identifyMaximalExtension,Ring,ZZ)
  Headline
    print code which identifies the maximal extension of a surface Y
  Usage
     identifyMaximalExtension(kk,k2)
  Inputs
    kk: Ring
       the ground field
    k2: ZZ
       the self-intersection number K_Y^2
  Outputs
     S: String
  Description
     Text
        Prints commands which help to identify the maximal extension
	of a 3-regular surface Y of codim 3 and degree 10 in P5
     Example   
	kk=ZZ/nextPrime(10^3)
	k2=-5
	identifyMaximalExtension(kk,k2)	
 ///

doc ///
  Key
    extensionsOfSpecialCurves   
    (extensionsOfSpecialCurves,Ring,ZZ)
  Headline
    print code which identifies the maximal extension of a randomly selected curve C 
  Usage
     extensionsOfSpecialCurves(kk,k2)
  Inputs
    kk: Ring
       the ground field
    k2: ZZ
       the self-intersection number K_Y^2
  Outputs
     S: String
  Description
     Text
        Prints commands which computes the maximal extensions of a random hyperplane section C
	of a 3-regular surface Y with K_Y^2 in {-2,-1}
     Example   
	kk=ZZ/nextPrime(10^3)
	k2=-2
	extensionsOfSpecialCurves(kk,k2)	
 ///


end

/// -- Coble surfaces
kk=ZZ/nextPrime 30
setRandomSeed("good decomposition 2")
P3=kk[x_0..x_3]
P4=kk[y_0..y_4]
h=random(P3^1,P3^{5:-2});
betti(X=ker map(P3,P4,h))
betti(X3=saturate ideal diff(basis(2,P4),gens X))
dim X3, genus X3
betti(X4=saturate ideal diff(basis(3,P4),gens X))
cX4=decompose X4
tally apply(cX4,c->(dim c, degree c))
pt=sub(syz transpose jacobian first cX4,kk)
betti(web=ideal(h*syz transpose pt))
P5=kk[z_0..z_5]
betti(Y1=reyeCongruence(web,P5))
ll=adjunctionProcess(Y1,1);
ll_0
minimalBetti(Y=ll_3)
--analyseFanoPolarizedEnriquesSurface(Y)
    P5:=ring Y;
    assert(dim P5==6);
    kk:=coefficientRing P5;
    assert(degree Y==10 and dim Y==3)
    G36:=kk[a_(0,0)..a_(2,2)]
    A:=transpose genericMatrix(G36,a_(0,0),3,3)
    sA:=A|diagonalMatrix({1,1,1})
    s= symbol s
    P2:=kk[s_0..s_2]
    P2xG36:=P2**G36
    betti(flag=sub(vars P2,P2xG36)*sub(sA,P2xG36)) 
    betti(Yf=sub(Y,flag))
    betti(m10x10=sub(contract(transpose sub(basis(3,P2),P2xG36),gens Yf),G36))
    betti(m10x10=map(G36^10,,sub(m10x10,G36)))
    elapsedTime betti (J=minors(2,m10x10)) -- 0.768897 seconds elapsed
    elapsedTime betti(gbJ=gens gb( J,DegreeLimit=>6))  -- 48.087 seconds elapsed
   -- elapsedTime dim J==0, degree J==20
    elapsedTime betti(J=trim ideal gbJ)  -- 125.084 seconds elapsed
    elapsedTime cJ=decompose J; -- 1773.67 seconds elapsed
    tally apply(cJ,c->(dim c, degree c))
    r=lcm apply(cJ,c->degree c)
    kke=GF(char kk,r,Variable=>symbol e)
    P5e=kke[gens P5]
    Ye=sub(Y,P5e);
    G36e=kke[gens G36]
    cJe=flatten apply(cJ,I->decompose sub(I,G36e));
    tally apply(cJe,c->(degree c, dim c))
    sAe=sub(sA,G36e);
    planeCubics=apply(cJe,c->(plane=ideal(vars P5e*sub(syz(sAe% c),kke));trim(plane+Ye)));
    tally apply(planeCubics,c->(dim c, degree c, betti c)) 
    curves=apply(planeCubics,c->decompose c);
    tally apply(curves,c->apply(c,d->degree d))
    curves1=flatten curves;
    curves2= select(curves1,c-> dim(c+minors(4,jacobian c))>0);
    singCurves=apply(curves2,c->saturate(c+minors(4,jacobian c)));
    apply
    elapsedTime curves3=apply(curves1,c->primaryDecomposition saturate(Ye+c^2));    
    tally apply(curves3,c->apply(c,d->(dim d,degree d)))
    curves4=apply(curves3,c->(first c));
    tally apply(curves4,c->(dim c, degree c, genus c))
    tally apply(curves4,c->(degree radical c, betti c))
    betti(nonHypSingY=saturate trim (Y+minors(2,jacobian Y)))
    betti(nonHypSingYr=radical nonHypSingY)
    (dim nonHypSingYr, degree nonHypSingYr)
    fourPts=decompose sub(nonHypSingYr,P5e)
    matrix apply(singCurves,c->apply(fourPts,d->dim(c+d)))
     apply(curves1,c->(degree c,apply(fourPts,d->dim(c+d))))
     curves=curves1;
     curvesDeg1=select(curves,c->degree c==1);
     curvesDeg2=select(curves,c->degree c==2);
     curvesDeg3=select(curves,c->degree c==3);
   #(curvesDeg1=unique curvesDeg1)
   #(curvesDeg2=unique curvesDeg2)
   curves=curvesDeg1|curvesDeg2|curvesDeg3;  
   M1=matrix apply(curves,c->(apply(curves,d->degree((c+d):sub(nonHypSingYr,P5e)))))  
   M2=matrix apply(curves,c->(apply(curves,d->degree((c+d)))))  
   M2-M1     
    L=matrix apply(planeCubics,c->apply(planeCubics,d->(if dim(c+d)==0 or dim(c+d)==2 then 0 else 1)))
    sL=LLL syz L
    ind={}
    scan(10,j->(pair=select(20,i->not sL_(i,j)==0);ind=ind|pair))
    ind
    L_ind^ind
    ind2={0,2,4,6,8,10,12,14,16,18}
    L2=(L_ind^ind)_ind2^ind2
    tenCubics=planeCubics_ind_ind2;
    betti(cub11=intersect tenCubics)
    ind1=if degrees source gens cub11==toList(11:{3}) then ind else ind_({1,0}|toList(2..19));
    tenCubics=planeCubics_ind1_ind2;    
    betti intersect tenCubics
    pencils=apply(tenCubics,F->(F2=saturate(F^2+Ye);
            h=F2_0;
            residual=(ideal h +Ye):F2;
            (gens residual)_{0,1}));
    tally apply(pencils,p->betti p)
    baseLoci=apply(pencils,p->saturate(ideal p +Ye));
    tally apply(baseLoci,b->(dim b, degree b, genus b, betti b))
    elapsedTime singBs=apply(baseLoci,b->trim(b+minors(4,jacobian b)));
    tally apply(singBs,c->dim c)
    tally apply(baseLoci,b->(twoB=saturate(b^2+Ye);(dim twoB,degree twoB,genus twoB)))
    betti res first baseLoci
    -- 14+1-9, binomial(5+2,2)-(28+1-9)
    -- 14*t+1-9+14*(t-1)+1-9 + deg NormalBundle == 28*t +1 -33
    --14+2*9-1-33
    -- t+1+(t+2+1)==2t+1-(-3) => in case of a nodal Enriques, 
    --                           the self-intersection numbers of the b's are -2
    matrix apply(tenCubics,c->apply(baseLoci,b->degree(c+b)))
    M=matrix apply(baseLoci,b1->apply(baseLoci,b2->if dim(b1+b2)==1 then degree(b1+b2) else
            if dim(b1+b2)==2 then -2 else 0))
    eigenvalues(M**RR)
    factor det M
    L2
    det L2
    eigenvalues L2



///

/// --Coble surfaces 2
kk=QQ
kk=ZZ/nextPrime 10^3
P3=kk[x_0..x_3]
h=basis(2,P3)
P9=kk[z_0..z_9]
v2=ker map(P3,P9,h)
minimalBetti v2
P33=kk[x_0..y_3]
hx=sub(h,P33)
hy=sub(h,(vars P33)_{4..7})
Z=ker map(P33,P9,hx+hy);
minimalBetti Z
hei=199
pts={matrix{{1,0,0,0}},matrix{{0,1,0,0}},matrix{{0,0,1,0}},matrix{{0,0,0,1}},matrix{{1,1,1,1}},random(ZZ^1,ZZ^4,Height=>hei)-matrix{toList(4:floor(hei/2))}}

betti (sixPts=intersect apply(pts,p->trim minors(2,sub(h,p)||vars P9)))
betti(L=ideal (gens sixPts)_{0..3})
Y=ideal (gens Z%L);
P5=kk[support Y];dim P5==6
Y=sub(Y,P5);
betti(nonHypSing=radical saturate(Y+minors(2,jacobian Y)))
ll=adjunctionProcess(Y,1);
ll_0,minimalBetti ll_3
degree nonHypSing
web =ideal( h*sub(jacobian L,kk))
betti res web
minimalBetti(Yr=reyeCongruence(web,P5))
ll=adjunctionProcess(Yr,1);
ll_0,minimalBetti(Y=ll_3)
ll=adjunctionProcess(Y,4);
ll_0
betti(nonHypSing=radical saturate(Y+minors(2,jacobian Y)))
degree nonHypSing
betti(nonHypSing=radical saturate(Yr+minors(2,jacobian Yr)))
degree nonHypSing
decompose nonHypSing

    assert(degree Y==10 and dim Y==3)
    G36:=kk[a_(0,0)..a_(2,2)]
    A:=transpose genericMatrix(G36,a_(0,0),3,3)
    sA:=A|diagonalMatrix({1,1,1})
    s= symbol s
    P2:=kk[s_0..s_2]
    P2xG36:=P2**G36
    betti(flag=sub(vars P2,P2xG36)*sub(sA,P2xG36)) 
    betti(Yf=sub(Y,flag))
    betti(m10x10=sub(contract(transpose sub(basis(3,P2),P2xG36),gens Yf),G36))
    betti(m10x10=map(G36^10,,sub(m10x10,G36)))
    elapsedTime betti (J=minors(2,m10x10)) -- 0.768897 seconds elapsed
    elapsedTime betti(gbJ=gens gb( J,DegreeLimit=>6))  -- 48.087 seconds elapsed
   -- elapsedTime dim J==0, degree J==20
   dim J, degree J
    elapsedTime betti(J=trim ideal gbJ)  -- 125.084 seconds elapsed
    elapsedTime cJ=decompose J; -- 1773.67 seconds elapsed
    tally apply(cJ,c->(dim c, degree c))
    r=lcm apply(cJ,c->degree c)
    kke=GF(char kk,r,Variable=>symbol e)
    P5e=kke[gens P5]
    Ye=sub(Y,P5e);
    G36e=kke[gens G36]
    cJe=flatten apply(cJ,I->decompose sub(I,G36e));
    tally apply(cJe,c->(degree c, dim c))
    sAe=sub(sA,G36e);
    planeCubics=apply(cJe,c->(plane=ideal(vars P5e*sub(syz(sAe% c),kke));trim(plane+Ye)));
    tally apply(planeCubics,c->(dim c, degree c, betti c)) 
    curves=apply(planeCubics,c->decompose c);
///



/// 
kk=ZZ/nextPrime(10^3)
kk=ZZ/19
    Z=maximalExtensionOfReyeFanoModel(kk,symbol z);
    P9= ring Z
    Y=ideal(gens Z%ideal random(P9^1,P9^{4:-1}));
P5=kk[support Y];Y=sub(Y,P5);
--(Y,pt)=fanoPolarizedEnriquesSurface(kk,symbol y);
minimalBetti Y
(A,B,eq)=extension(Y,2);
eq
dim ring eq -- ==6
analyseFanoPolarizedEnriquesSurface(Y)
P5:=ring Y;
    assert(dim P5==6);
    kk:=coefficientRing P5;
    assert(degree Y==10 and dim Y==3)
    G36:=kk[a_(0,0)..a_(2,2)]
    A:=transpose genericMatrix(G36,a_(0,0),3,3)
    sA:=A|diagonalMatrix({1,1,1})
    s= symbol s
    P2:=kk[s_0..s_2]
    P2xG36:=P2**G36
    betti(flag=sub(vars P2,P2xG36)*sub(sA,P2xG36)) 
    betti(Yf=sub(Y,flag))
    betti(m10x10=sub(contract(transpose sub(basis(3,P2),P2xG36),gens Yf),G36))
    betti(m10x10=map(G36^10,,sub(m10x10,G36)))
    elapsedTime betti (J=minors(2,m10x10)) -- 0.768897 seconds elapsed
    elapsedTime betti(J=trim J)  -- 1480.41 seconds elapsed for general Enriques

    elapsedTime betti(gbJ=gens gb( J,DegreeLimit=>6))   -- 86.3892 seconds elapsed
    dim J==0, degree J==20
    betti(J=trim ideal gbJ)
    elapsedTime cJ=decompose J;
    tally apply(cJ,c->(dim c, degree c))
    r=lcm apply(cJ,c->degree c)
    kke=GF(char kk,r,Variable=>symbol e)
    P5e=kke[gens P5]
    Ye=sub(Y,P5e);
    G36e=kke[gens G36]
    cJe=decompose sub(J,G36e);
    tally apply(cJe,c->(degree c, dim c))
    sAe=sub(sA,G36e);
    planeCubics=apply(cJe,c->(plane=ideal(vars P5e*sub(syz(sAe% c),kke));trim(plane+Ye)));
    tally apply(planeCubics,c->(dim c, degree c, betti c)) 
    L=matrix apply(planeCubics,c->apply(planeCubics,d->(if dim(c+d)==0 or dim(c+d)==2 then 0 else 1)))
    sL=LLL syz L
    ind={}
    scan(10,j->(pair=select(20,i->not sL_(i,j)==0);ind=ind|pair))
    ind
    L_ind^ind
    ind2={0,2,4,6,8,10,12,14,16,18}
    L2=(L_ind^ind)_ind2^ind2
    tenCubics=planeCubics_ind_ind2;
    betti(cub11=intersect tenCubics)
    ind1=if degrees source gens cub11==toList(11:{3}) then ind else ind_({1,0}|toList(2..19));
    tenCubics=planeCubics_ind1_ind2;    
    betti intersect tenCubics
    pencils=apply(tenCubics,F->(F2=saturate(F^2+Ye);
            h=F2_0;
            residual=(ideal h +Ye):F2;
            (gens residual)_{0,1}));
    tally apply(pencils,p->betti p)
    baseLoci=apply(pencils,p->saturate(ideal p +Ye));
    tally apply(baseLoci,b->(dim b, degree b, genus b, betti b))
    elapsedTime singBs=apply(baseLoci,b->trim(b+minors(4,jacobian b)));
    tally apply(singBs,c->dim c)
    tally apply(baseLoci,b->(twoB=saturate(b^2+Ye);(dim twoB,degree twoB,genus twoB)))
    betti res first baseLoci
    -- 14+1-9, binomial(5+2,2)-(28+1-9)
    -- 14*t+1-9+14*(t-1)+1-9 + deg NormalBundle == 28*t +1 -33
    --14+2*9-1-33
    -- t+1+(t+2+1)==2t+1-(-3) => in case of a nodal Enriques, 
    --                           the self-intersection numbers of the b's are -2
    matrix apply(tenCubics,c->apply(baseLoci,b->degree(c+b)))
    M=matrix apply(baseLoci,b1->apply(baseLoci,b2->if dim(b1+b2)==1 then degree radical(b1+b2) else
            if dim(b1+b2)==2 then -2 else 0))
    eigenvalues(M**RR)
    factor det M
    L2
    det L2
    eigenvalues L2
    M1=lift(1/2*sub(M,QQ),ZZ)
    factor det M1
    eigenvalues(M1**RR)
    (eigval,eigvect)=eigenvectors(M1**RR,Hermitian=>true)
    eigvect*transpose eigvect
    transpose eigvect*M1*eigvect
///

///
--attempt to construct a surface Y with K_Y^2=-4 which extends further than P7
-- idea: to choose 6 pts on Y1 which move in a pencil on C
-- the construction fails
kk=ZZ/nextPrime(10^3)
P2=kk[x_0..x_2]
pts={matrix{{1,0,0}},matrix{{0,1,0}},matrix{{0,0,1}},matrix{{1,1,1}}}
Ipts=apply(pts,p->trim(minors(2,vars P2||p)))
betti(h1=intersect(Ipts|{ideal(basis(3,P2))}))
P5=kk[y_0..y_5]
h1=gens Ipts_0** gens intersect(drop(Ipts,1))
delPezzo=trim ker map(P2,P5,h1);
minimalBetti delPezzo
fdelPezzo=res delPezzo
IP1xP2=minors(2,fdelPezzo.dd_2_{1,4}^{1,2,4})
minimalBetti IP1xP2
--plane=trim ideal(fdelPezzo.dd_2_{0})
fourPts=apply(4,i->(
	while (
	fivePts=decompose(delPezzo+ideal random(P5^1,P5^{2:-1}));
    	kkPts=select(fivePts, c->degree c == 1);
	#kkPts==0) do ();
    	first kkPts))
betti(IfourPts=intersect(fourPts))
q=gens IfourPts*random(source gens IfourPts,P5^{-2})
C=ideal(q)+delPezzo
minimalBetti C
H=gens IfourPts*random(source gens IfourPts,P5^{-1})
betti(sixPts=(C+ideal H):IfourPts)
degree sixPts, dim sixPts
minimalBetti(Y1=IP1xP2+ideal q)
q2=ideal(gens C*random(source gens C,P5^{-2}))
betti(residual=(Y1+q2):C)
betti sixPts
betti (gens intersect(residual,sixPts))

betti(h2=gens trim ideal ((gens intersect(residual,sixPts))%Y1))
PY1=P5/Y1
phi=map(PY1,P5,h2)
betti(Y=trim ker phi)
dim Y, degree Y, genera Y
minimalBetti Y
-- => the construction of Y fails, why remains unclear.
elapsedTime betti(singY=trim(Y+minors(3,jacobian Y)))
dim singY, degree singY
betti(singYr=saturate singY)
csingY=decompose singYr
hess=diff(vars P5,transpose diff(vars P5,Y_0))
rank hess

sixPts1=apply(6,i->(
	while (
	fivePts=decompose(delPezzo+ideal random(P5^1,P5^{2:-1}));
    	kkPts=select(fivePts, c->degree c == 1);
	#kkPts==0) do ();
    	first kkPts))
betti(IsixPts1=intersect sixPts1)
q=gens IsixPts1*random(source gens IsixPts1,P5^{-2})
C=ideal(q)+delPezzo
minimalBetti C
minimalBetti(Y1=IP1xP2+ideal q)
q2=ideal(gens C*random(source gens C,P5^{-2}))
betti(residual=(Y1+q2):C)
betti(h3=trim ideal((gens intersect(residual,IsixPts1))%Y1))
PY1=P5/Y1
phi=map(PY1,P5,gens h3)
betti(Y=trim ker phi)
dim Y, degree Y, genera Y
minimalBetti Y
(A,B,eq)=extension(Y,2);
eq
dim ring A
///

     


))
    -- rank 4 quadic in the ideal of a canonical curve
    kk=ZZ/nextPrime(10^3)
    P5=kk[x_0..x_5]
    m=random(P5^5,P5^{5:-1});m=m-transpose m;
    delPezzo =pfaffians(4,m);
    minimalBetti delPezzo
    C=delPezzo+ideal random(2,P5);
    P5t=kk[t_0..t_5]
    P5xP5=P5**P5t
    betti(qt=sub(gens C,P5xP5)*transpose sub(vars P5t,P5xP5))
    varsP5=sub(vars P5,P5xP5)
    hess=sub( diff(varsP5,transpose(diff(varsP5,qt))),P5t)
    betti(rk4qs=trim minors(5,hess))
    dim rk4qs, degree rk4qs
    minimalBetti rk4qs
    betti(rk4pf=saturate trim ideal (gens rk4qs%ideal P5t_5))
    minimalBetti rk4pf
    dim rk4pf, degree rk4pf
    elapsedTime crk4pf=decompose rk4pf;
    tally apply(crk4pf,c->(degree c,dim c))
    betti(rk4pfr=radical rk4pf)
    betti(fivePlanes=rk4pfr+ideal(P5t_5))
    dim fivePlanes, degree fivePlanes 
    elapsedTime betti(rk4rest=rk4qs:fivePlanes)
    degree rk4rest, dim rk4rest
    minimalBetti rk4rest, codim rk4rest
    betti(frk4rest=res( rk4rest,FastNonminimal=>true))
    betti(m4=prune coker transpose frk4rest.dd_4)
    betti(I4=ann m4), (dim I4,degree I4)
    elapsedTime betti(rest=rk4rest:I4)
    rest == rk4rest
    betti(cycles=syz transpose frk4rest.dd_4)
elapsedTime    betti(ext3=prune subquotient(cycles, transpose frk4rest.dd_3))   -- 449.309 seconds elapsed 
    minimalBetti ext3
    betti frk4rest
    betti(frk4qs=res(rk4qs))
    codim rk4qs
    betti(adj=adjointMatrix(frk4qs.dd_3,symbol z))
    P14=ring adj,dim P14==15
    betti(J=ann coker adj)

restart
loadPackage( "SurfacesAndExtensions",Reload=>true)

randomPoints=method(Options=>{Height=>19})
randomPoints(ZZ,Ring):= opt -> (d,Pn) -> (
    -- d, number of points 
    -- Pn, coordinate ring of Pn
    m:= dim Pn;
    h:=opt.Height;
    mean:=floor(h/2);
    L:={};pt:=null,Ipt:=null;
    scan(d,i->(
	    pt=matrix{apply(m,j->random(ZZ,Height=>h)-mean)};
	    Ipt=ideal(vars Pn*syz pt);
	    L=append(L,Ipt)));
    L)
TEST///
P2=QQ[t_0..t_2]
npts=6
while(
    points=randomPoints(npts,P2,Height=>3);
    not degree intersect points==npts) do ()
x=symbol x

betti(I=rationalSurface(points,3,toList(6:1),x))
I_0
P2=QQ[t_0..t_2]
points=randomPoints(14,P2,Height=>9)
///





restart
loadPackage( "SurfacesAndExtensions",Reload=>true)

uninstallPackage("SurfacesAndExtensions")
restart
installPackage("SurfacesAndExtensions")
 
viewHelp SurfacesAndExtensions

kk=ZZ/nextPrime(10^2)
P5=kk[x_0..x_5]
m1=matrix apply(5,i->apply(5,j-> if i< j then (if i==0 and j>1 then x_(j-2) else 
	if i==1 then x_(i+j) else if i>1 then random(1,P5) else 0) else 0))
m=m1-transpose m1
dP=pfaffians(4,m)
q=matrix{{random(2,P5)%dP}}
gens dP|q
T=kk[t_0..t_5]
P5xT=P5**T
qt=sub(vars T,P5xT)*transpose sub(gens dP|q,P5xT)
hess=map(T^6,,sub(diff(sub(vars P5,P5xT),transpose diff(sub(vars P5,P5xT),qt)),T))
betti(rk4=trim minors(5,hess))
dim rk4, degree rk4
R=kk[s_0..t_5]
ss=(vars R)_{0..5}
rk4a=sub(rk4,R);
rk4b=sub(rk4,ss);
rk4c=sub(rk4,ss+(vars R)_{6..11});
betti(trisec1=trim(rk4a+rk4b+rk4c))
betti(diag=minors(2,ss||(vars R)_{6..11}))
elapsedTime betti(trisec2=trisec1:ideal(diag_14))
