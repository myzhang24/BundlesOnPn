newPackage(
    "BundlesOnPn",
    Version => "1.0",
    Date => "Oct 2019",
    Authors => {{Name => "Mengyuan Zhang",
	    Email => "myzhang@berkeley.edu",
	    HomePage => "https://math.berkeley.edu/~myzhang/"}},
    Headline => "Bundles On Pn with vanishing lower cohomologies",
    DebuggingMode => true    
    )

export {
    "isBundleSequence",
    "bundleSequences",
    "minBetti",
    "isAdmissible",
    "maxBetti"
}
    
isBundleSequence = method()
isBundleSequence(ZZ,List) := (n,L) -> (
    --check if a sequence L is a bundle sequence on Pn
    if #L == 0 then return false;
    D := (L | {last L}) - ({0} | L);
    L#0 >0 and L#-1 != L#-2 and all(#D, i -> if D#i < 0 then L#i >= n else true)    
)
bundleSequences = method()
bundleSequences(ZZ,ZZ,ZZ) := (n,r,d) -> (
    --produces bundles of rank r and degree <= d on Pn
    if d < r then return {};
    if d == r then return {{r}};
    if d > r then (
    	L := flatten apply(splice{1..d-r}, i ->
	        apply(bundleSequences(n,r,d-i), B -> (
			if #B == 1 and i == r then return null;
		    	if i > first B and first B < n then null else prepend(i,B)
			)) 
	);
    	prepend({r},delete(null,L))
    )
)
minBetti = method()
minBetti List := B -> (
    --computes the normalized minimal Betti numbers with a given bundle seuqence B
    H := (B | {last B}) - ({0} | B);
    a := flatten apply(#H, i -> if H#i < 0 then splice{(-H#i):i} else {});
    b := flatten apply(#H, i -> if H#i > 0 then splice{H#i:i} else {});
    c1 := sum(a) - sum(b);
    (apply(a, i-> i+ceiling(c1/last B)), apply(b,i->i+ceiling(c1/last B))) 
)
isAdmissible = method()
isAdmissible(ZZ,List,List) := (n,a,b) -> (
    --checks if a pair of sequences is admissible
    if #a == 0 then return true;
    if #b < #a+n then return false;
    (a,b) = (sort a, sort b);
    all(#a, i -> a_i > b_(i+n))    
)
maxBetti = method()
maxBetti (ZZ,ZZ,List) := (n,d,B) -> (
    --computes the maximal Betti numbers with bundle sequence B
    -- up to regularity d on Pn
    (a,b) := minBetti B;
    L := (a,b);
    if #b < n then return L;
    for i from 1+b_n to d do (
    	while (
	    T := (sort prepend(i, first L), sort prepend(i,last L));
	    isAdmissible(n,first T, last T)    
	) do (L = T;);	
    );
    L    
)
random(Ring,Matrix) := opts -> (R,M) -> (
    --generates random minimal matrix with forms of given degrees
    assert(ring M === ZZ);
    matrix apply(numrows M, i -> apply(numcols M, j-> 
	    if M_(i,j) == 0 then 0_R else random(M_(i,j),R)))    
)

beginDocumentation()

doc ///
       Key
         BundlesOnPn
       Headline
         Bundles On Pn with vanishing lower cohomologies
       Description
        Text
          Bundles On Pn with vanishing lower cohomologies and methods of generating them in a 
	  systematic way were described in the paper
	  
	   {\em Bundles On Pn with vanishing lower cohomologies},
	   \url{https://math.berkeley.edu/~myzhang/papers/BundlesOnPnWithVanishingLowerCohomologies.pdf} .
	  
	  This package includes the codes to produce bundle sequences up to a given degree.
	  It also provides methods to generate the maximal and minimal element of the lattice of
	  Betti numbers described in the above paper.
	  
	  Once the Betti numbers (a,b) are give, we can produce a minimal matrix of random forms
	  in corresponding degrees that gives a presentation of a bundle with vanishing lower 
	  cohomologies on Pn.
        Example
	  R = (ZZ/101)[x,y,z,w]
	  L = bundleSequences(3,3,8)
	  (a,b) = minBetti last L
	  E = coker random(R,transpose matrix apply(#a,i->apply(#b,j-> a#i-b#j)))
     ///

doc ///
       Key
         (isBundleSequence,ZZ,List)
       Headline
         checks whether a sequence is a bundle sequence
       Usage
         b = isBundleSequence(n,L)
       Inputs
         n:ZZ
           positive
         L:List
           of integers
       Outputs
         b:Boolean
       Description
        Text
          Checks whether a list of integers is a bundle sequence on Pn.
        Example
          isBundleSequence(3,{6,3})
	  isBundleSequence(4,{6,3})
       SeeAlso
         bundleSequences
     ///

doc ///
       Key
         bundleSequences
         (bundleSequences,ZZ,ZZ,ZZ)
       Headline
         produces bundle sequences to a given degree
       Usage
         L = bundleSequence(n,r,d)
       Inputs
         n:ZZ
           dimension of ambient projective space
         r:ZZ
           rank of the bundle sequences
	 d:ZZ
	   degree bound of the bundle sequences
       Outputs
         L:List
	   of bundle sequences on Pn of rank r and degree <= d
       Description
        Text
          This function generates all bundle sequences on Pn of rank r and degree <= d
	  recursively.
        Example
          bundleSequences(3,4,9)
       SeeAlso
          isBundleSequence
     ///

doc ///
       Key
         isAdmissible
         (isAdmissible,ZZ,List,List)
       Headline
         checks whether a pair of integer sequences is admissible
       Usage
         b = isAdmissible(n,A,B)
       Inputs
         n:ZZ
           dimension of ambient projective space
         A:List
           the degrees of syzygies
	 B:List
	   the degrees of generators
       Outputs
         b:Boolean
       Description
        Text
          This functions checks whether a pair of integer sequences (A,B) is admissible on Pn. 
        Example
          isAdmissible(2,{1,1},{0,0,0,0})
     ///

doc ///
       Key
         minBetti
         (minBetti,List)
       Headline
         produces the minimal normalized Betti numbers of a bundle sequence
       Usage
         (a,b) = minBetti B
       Inputs
         B:List
           bundle sequence
       Outputs
	 a:List
           degrees of syzygies
	 b:List
	   degrees of generators
       Description
        Text
          This function returns the minimal Betti numbers among all normalized bundles
	  with a given bundle sequence.
        Example
          minBetti {6,4}
       SeeAlso
          maxBetti
     ///
     
doc ///
       Key
         maxBetti
         (maxBetti,ZZ,ZZ,List)
       Headline
         produces the maximal Betti numbers
       Usage
         (a,b) = maxBetti(n,d,B)
       Inputs
	 n:ZZ
	   dimension of the ambient projective space
	 d:ZZ
	   regularity bound
	 B:List
           bundle sequence
       Outputs
	 a:List
           degrees of syzygies
	 b:List
	   degrees of generators
       Description
        Text
          This function returns the maximal Betti numbers among all normalized bundles
	  on Pn with a given bundle sequence up to a given regularity.
        Example
          maxBetti(3,4,{6,4})
       SeeAlso
          minBetti
     ///
     
doc ///
       Key
         (random,Ring,Matrix)
       Headline
         produces a minimal matrix of random forms
       Usage
         N = random(R,M)
       Inputs
	 R:Ring
	 M:Matrix
	   of integers specifying the degrees of the random forms of R
       Outputs
	 N:Matrix
	   of random forms in R of degrees specified by M
       Description
        Text
          This function produces a matrix of random forms in a ring R
	  whose degrees are given by a matrix of integers
        Example
          random(ZZ[x,y],matrix{{1,1,2},{2,1,1}})
     ///
     


TEST ///
L = bundleSequences(3,5,7);
assert(isbundleSequence(3,last L))
///



end


--
restart
uninstallPackage "BundlesOnPn"
installPackage "BundlesOnPn"
viewHelp "BundlesOnPn"

