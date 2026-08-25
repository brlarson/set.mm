$( SFS.mm $)

$( Metamath theorems and definitions for Supplemental Formal Semantics $)

$( read-in Metamath database of theorems and proofs $)
$[ set.mm $]



$( 
###############################################################################
  Theorems for BLESS
###############################################################################

The Behavior Language for Embedded Systems with Software (BLESS) allows programs
which control machines to be proved correct.  Programs are annotated with
assertions to form a proof outline.  

The BLESS Proof Assstant transforms BLESS programs having proof outlines into
deductive proofs.  Theorems in proofs are Hoare Triples of the form:
<<P>> S <<Q>> where <<P>> and <<Q>> are formulas in BLESS Logic, and S is a 
formula in an interval temporal logic satisfied by lattices of states.

Computation creates a satisfying lattice for S such that <<P>> on the start 
state of S and <<Q>> holds on the end state of S.  Because a sequence is also
a lattice, you can think of S as a traditional imperative program.  However
lattices entail a partial order which can be exploited by multicore CPUs.

Each theorem in a deductive proof is either a tautology, given, or derived by
an inference rule from prior theorems.  Many of the theorems arise from formal
semantics of BLESS language constructs.  Almost all of the others have soundness 
proofs in Metamath (the others involve things like adding parentheses).  Each
theorem includes a natural language explanation, and reference to definitional 
or Metamath theorems.

The BLESS Book containing LaTeX for each of the Metamath theorems used in BLESS
proofs can be found at multitude.net.

The BLESS IDE and Proof Assistant can be automatically installed in the Open-
Source AADL Tool Environment (OSATE) available at osate.org.  AADL is Arch-
itecture Analysis and Design Language (SAE International standard AS5506D) for
systems engineering of safety-critical cyberphysical systems.

Example AADL architectures having BLESS specifications, behaviors and correct-
ness proofs can be found at https://github.com/brlarson/BLESS-models.git


$)


$( brackets for wff substitution $)
$c [- ]- $.  $( similar to [_ ]_ for proper substitution of class into class csb $)

$( starting constants of multi-term conjunction and disjunction $)
$c /\( \/( $.

$( starting constants of multi-term addition and multiplication $)
$c +( *( $.

$( closing parenthesis for multi-term constructs $)
$c )x $.

$( BLESS Logic $)
$c mathfrakM $. 
$c boldI $.
$c @ ^. $. $( at and caret $)
$c b~< b~<= PRED TERM VAR PROP I_t $.
$c CON FUNC $.
$c [[ ]] $.

$( wff-list:  define constant 'lw' to designate lists of well-formed
	formulas, just like 'wff' designates well-formed
	formulas  $)
$c lw $.

$( tuple brackets $)
$c  <.. >.. $.

$( assertion brackets $)
$c b<< b>> $.

$( variable time $)
$v t_0 t_1 t_2 t_3 t_r $.
$c now tops $.

$(  Domain of time. $)
$c TIME $.

$( not models $)
$( $c nmodels $. $)

$(  create a class list type $)
$c bcl $.
$v cl_1 cl_2 $. 

$( directed binary graph $)
$c DBG $. 

$( identifier class $)
$c ID $.
$( Define class of letters: Letter: ('a'..'z'|'A'..'Z'); $)
$c Letter $.
$( Define class of digits:  Digit     :  ( '0'..'9' ) ; $)
$c Digit $.
$( Define class of all charaters that can be in strings $)
$c QWERTY $.
$( Define set of all enumeration types $)
$c Enum $.

$( assertions $)
$c P_ P_1 P_2 P_3 P_n Q_ Q_1 Q_2 Q_3 Q_n $.

$( asserted actions $)
$c AA_1 AA_2 AA_3 AA_n $.

$( actions $)
$c S__ S_1 S_2 S_3 S_n $.

$( quantity type $)
$c QT $.
$( array type $)
$c Array $.
$( record type $)
$c Record $.
$( variant type $)
$c Variant $.
$( type $)
$c Type $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       BLESS Helpers 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( P and Q implies P or R.  $)
bl.an2impor2  $p  |- ( ( ph /\ ps ) -> ( ph \/ ch ) )
  $=  ( wa wo simpl orc syl ) ABDAACEABFACGH $.  
   $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.an2impor2 $)   

$( Law of And-Simplification: P and (Q or P) is P. $)
bl.PandQorPisP $p |- ( ( ph /\ ( ps \/ ph ) ) <-> ph )
  $= ( wo wa wb pm4.45 bicom orcom anbi2i bibi1i bitri mpbi ) AAABCZDZE
  ZABACZDZAEZABFONAERANGNQAMPAABHIJKL $.

$( Law of And-Simplification: P and (P or Q) is P. $)
bl.PandPorQisP $p |- ( ( ph /\ ( ph \/ ps ) ) <-> ph )
  $= ( wo wa wb bl.PandQorPisP orcom anbi2i bibi1i mpbi ) ABACZDZAEAABC
  ZDZAEABFLNAKMABAGHIJ $.   

$( Law of And-Simplification: P is P and (Q or P). $)
bl.PisPandQorP $p |- ( ph <-> ( ph /\ ( ps \/ ph ) ) )
  $= ( wo wa wb pm4.45 orcom anbi2i bibi2i mpbi ) AAABCZDZEAABACZDZEABF
  LNAKMAABGHIJ $.   

$( Law of Or-Simplification: P or (Q and P) is P. $)
bl.PorQandPisP $p |- ( ( ph \/ ( ps /\ ph ) ) <-> ph )
  $= ( wa wo wb pm4.44 bicom ancom orbi2i bibi1i bitri mpbi ) AAABCZDZE
  ZABACZDZAEZABFONAERANGNQAMPAABHIJKL $.
     
$( Law of Or-Simplification: P or (P and Q) is P. $)
bl.PorPandQisP $p |- ( ( ph \/ ( ph /\ ps ) ) <-> ph )
  $= ( wa wo wb bl.PorQandPisP ancom orbi2i bibi1i mpbi ) ABACZDZAEAABC
  ZDZAEABFLNAKMABAGHIJ $.   
          
$( Law of Or-Simplification: P is P or (Q and P). $)
bl.PisPorQandP $p |- ( ph <-> ( ph \/ ( ps /\ ph ) ) )
  $= ( wa wo wb pm4.44 ancom orbi2i bibi2i mpbi ) AAABCZDZEAABACZDZEABF
  LNAKMAABGHIJ $.

${
    bl.cd.1  $e |- ( ph -> ps ) $.
    bl.cd.2  $e |- ( ch -> th )  $.
    bl.cd.3  $e |- ( ph \/ ch ) $.
  $( Constructive Dilemma. $)
  bl.cd $p |- ( ps \/ th )
    $=  ( wo orim12i ax-mp ) ACHBDHGABCDEFIJ $.
$}

${
    $d A x $.
    $d B x $.
    $d k x $.
    bl.ralssi.1 $e |- A C_ B $.
  $( Restriction of universal quantification to a subset. $)
  bl.ralssi $p |- ( A. x e. A ph <-> A. x e. A ( x e. B /\ ph ) )
    $= ( cv wcel wa wral r19.26 wtru wss dfss3 bitru anbi1i truconj
    bitr4i mpbi bitr2i ) BFDGZAHBCITBCIZABCIZHZUBTABCJUCKUBHUBUAKUBUACD
    LUAEBCDMRNOUBPQS $.
$}

${
		bl.addass4i.1 $e |- A e. RR $.
		bl.addass4i.2 $e |- B e. RR $.
		bl.addass4i.3 $e |- C e. RR $.
		bl.addass4i.4 $e |- D e. RR $.
  $( Associative Law for Addition, four terms. $)
  bl.addass4i $p |- ( ( ( A + B ) + C ) + D ) = ( ( A + B ) + ( C + D ) )
    $= ( caddc co recni addcli addassi ) ABIJCDABAEKBFKLCGKDHKM $.
$}

$( Conjunction with False on the Left. $)	
bl.anfal $p |- ( ( F. /\ ph ) <-> F. )
  $=  ( wfal wa fal intnanr bifal ) BACBADEF $.

$( Conjunction with False on the Right. $)
bl.anfar $p |- ( ( ph /\ F. ) <-> F. ) 
  $=  ( wfal wa fal intnan bifal ) ABCBADEF $.

$( Disjunction with True on the Left. $)
bl.ortrl $p  |- ( ( T. \/ ph ) <-> T. )
  $= ( wtru wo tru orci bitru ) BACBADEF $.

$( Disjunction with True on the Right. $)
bl.ortrr $p  |- ( ( ph \/ T. ) <-> T. )
  $=  ( wtru wo tru olci bitru ) ABCBADEF $.
    
$( Superfluity of Equivalence. $)
bl.seq $p |- ( ( ph <-> T. ) -> ph )
   $= ( wtru wb wi biimpr trut biimpri syl ) ABCBADZAABEAIAFGH $.


  ${
  bl.adddii.1 $e |- A e. RR $.
  bl.adddii.2 $e |- B e. RR $.
  bl.adddii.3 $e |- C e. RR $.
$( Distributive law for ` RR `. $)
bl.adddii $p |- ( A x. ( B + C ) ) = ( ( A x. B ) + ( A x. C ) ) 
  $= ( cr wcel cc recn ax-mp adddii ) ABCAGHAIHDAJKBGHBIHEBJKCGHCIHFCJK
  L $.  
  $}
  
  ${
  bl.adddizi.1 $e |- A e. ZZ $.
  bl.adddizi.2 $e |- B e. ZZ $.
  bl.adddizi.3 $e |- C e. ZZ $.
$( Distributive law for ` ZZ `. $)
bl.adddizi $p |- ( A x. ( B + C ) ) = ( ( A x. B ) + ( A x. C ) ) 
  $= ( cz wcel cc zcn ax-mp adddii ) ABCAGHAIHDAJKBGHBIHEBJKCGHCIHFCJKL
  $.  
  $}

    
$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Well-formed formula substitution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$( Substitution of a WFF by a WFF in a WFF $)
wsbw $a wff [- ps / ch ]- ph $.


$( Define substitution of a WFF by a WFF in a WFF $)
df-bl.sbw $a |- ( [- ps / ch ]- ph <-> ( ( ch <-> ps ) -> ph ) ) $.

 
$(  Substitution by the Same WFF has no Effect $)
bl.sbwid $p |- ( [- ps / ps ]- ph <-> ph )
	$= 
	$( wffs for bitri $)
	  wph wps wps wsbw  $( ph= [- ps / ps ]- ph $)
	  wps wps wb wph wi  $( ps= ( ( ps <-> ps ) -> ph ) $)
	  wph  $( ch= ph  $)
	$( use df-bl.sbw with ph= ph  ps= ps and ch= ps
	to make A: |- ( [ ps / ps ] ph <-> ( ( ps <-> ps ) -> ph ) )   $)
	wph wps wps df-bl.sbw
	$( wffs fo bicomi $)
	  wph  $( ph= ph $)
	  wps wps wb wph wi  $( ps= ( ( ps <-> ps ) -> ph ) $)
	$( wffs for a1bi $)
	  wps wps wb  $( ph= ( ps <-> ps ) $)
	  wph  $( ps= ph $)
		$( use biid
		to make |- ( ps <-> ps )  $)
		wps biid
	$( use a1bi with ph= ( ps <-> ps )  and ps= ph 
	to make |- ( ph <-> ( ( ps <-> ps ) -> ph ) )  $)
	a1bi
	$( use bicomi with ph= ph and  ps= ( ( ps <-> ps ) -> ph )
	to make B: |- ( ( ( ps <-> ps ) -> ph ) <-> ph ) $)
	bicomi
	$( use bitri with |- A:  and  |- B:
		|- ( ph -> ps )  and  |- ( ps <-> ch )  =>  |- ( ph -> ch )
		with ph= [- ps / ps ]- ph   ps= ( ( ps <-> ps ) -> ph )  ch= ph  
	to make |- ( [- ps / ps ]- ph <-> ph ) $)	
	bitri
	$( |- ( [- ps / ps ]- ph <-> ph ) $)
	$.
$( end of bl.sbwid $)

${
bl.bisbwl.1 $e |- ( ch <-> ps ) $.
$(  Equivalence of WFF Substitution on Left $)
bl.bisbwl $p |- ( [- ps / ch ]- ph <-> ph ) 
	$= 
	$( wffs for bitr4i  $)
	  wph wps wch wsbw  $( ph= [- ps / ch ]- ph $)
	  wch wps wb wph wi  $( ps= ( ( ch <-> ps ) -> ph ) $)
	  wph  $( ch= ph $)
	$( by df-bl.sbw
	  A:  |- ( [- ps / ch ]- ph <-> ( ( ch <-> ps ) -> ph ) )  $)
	wph wps wch df-bl.sbw
	$( wffs for a1bi $)
	  wch wps wb  $( ph= ( ch <-> ps ) $)
	  wph  $( ps= ph $)
	bl.bisbwl.1  $( |- ( ch <-> ps ) $)
	$( by a1bi with ph= ( ch <-> ps )  and ps= ph
		make B:  |- ( ph <-> ( ( ch <-> ps ) -> ph ) ) $)
	a1bi
	$( by bitr4i with ph= [- ps / ch ]- ph   ps= ( ( ch <-> ps ) -> ph )  and  ch= ph
		A: |- ( ph <-> ps )  and  B:  |- ( ch <-> ps ) $)
	bitr4i
	$( |- ( [- ps / ch ]- ph <-> ph )  $)
	$.
$}
$( end of bl.bisbwl $)

${
bl.bisbwr.1 $e |- ( ch <-> ps ) $.
$(  Equivalence of WFF Substitution on Right $)
bl.bisbwr $p |- ( ph <-> [- ps / ch ]- ph ) 
	$= 
	$( wffs for bicomi $)
	  wph wps wch wsbw  $( ph= [- ps / ch ]- ph $)
	  wph  $( ps= ph $)
	$( wffs for bl.bisbwl $)
	wph wps wch 
	bl.bisbwr.1 $( |- ( ch <-> ps ) $)  
	$( by bl.bisbwl |- ( [- ps / ch ]- ph <-> ph ) $)
	bl.bisbwl
	$( by bicomi with ph= [- ps / ch ]- ph  and  ps= ph $)
	bicomi
	$( |- ( ph <-> [- ps / ch ]- ph ) $)
	$.
$}
$( end of bl.bisbwr $)

${
bl.sylsbw.1 $e |- ( ph -> ps ) $.
bl.sylsbw.2 $e |- ( ch <-> th ) $.
$(  Syllogism of WFF Substitution Introduction into Inference $)
bl.sylsbw $p |- ( [- th / ch ]- ph -> [- th / ch ]- ps ) 
	$=
	$( wffs for 3imtr4i $)
	  wch wth wb wph wi  $( ph= ( ( ch <-> th ) -> ph ) $)
	  wch wth wb wps wi  $( ps= ( ( ch <-> th ) -> ps ) $)
	  wph wth wch wsbw  $( ch= [- th / ch ]- ph $)
	  wps wth wch wsbw  $( th= [- th / ch ]- ps $)
	$( wffs for imi2i $)
	  wph  $( ph= ph $)
	  wps  $( ps= ps $)
	  wch wth wb  $( ch= ( ch <-> th ) $)
	bl.sylsbw.1
	$( using imim2i   |- ( ph -> ps ) => |- ( ( ch -> ph ) -> ( ch -> ps ) ) 
		on bl.sylsbw.1 |- ( ph -> ps )
		with ph= ph  ps= ps  ch= ( ch <-> th )
		make A:  |- ( ( ( ch <-> th ) -> ph ) -> ( ( ch <-> th ) -> ps ) )  $)
	imim2i	
	$( using df-bl.sbw  with ph= ph  and  ps= th  and ch= ch
		make  B:  |- ( [- th / ch ]- ph <-> ( ( ch <-> th ) -> ph ) ) $)
	  wph wth wch
	df-bl.sbw
	$( using df-bl.sbw  with ph= ph  and  ps= th  and ch= ch
		make C: |- ( [- th / ch ]- ps <-> ( ( ch <-> th ) -> ps ) ) $)
	  wps wth wch
	df-bl.sbw
	$( chain A: B: and C: with 3imtr4i
		A: |- ( ph -> ps )  and  B: |- ( ch <-> ph )  and  
		C: |- ( th <-> ps )  =>  |- ( ch -> th )
		with ph= ( ( ch <-> th ) -> ph )  ps= ( ( ch <-> th ) -> ps )  
		  ch= [- th / ch ]- ph  th= [- th / ch ]- ps $)
	3imtr4i	  
	$( |- |- ( [- th / ch ]- ph -> [- th / ch ]- ps )  $)
	$.
$}
$( end of bl.sylsbw $)
$( this theorem was verified on first draft;  brl 4/1/2011  $)

${
bl.sbwsyl.1 $e |- ( [- th / ch ]- ph -> [- th / ch ]- ps ) $.
bl.sbwsyl.2 $e |- ( ch <-> th ) $.
$( Syllogism of WFF Substitution Elimination from Inference $)
bl.sbwsyl $p |- ( ph -> ps )
	$=
	$( wffs for ax-mp $)
	  wch wth wb  $( ph= ( ch <-> th ) $)
	  wph wps wi  $( ps= ( ph -> ps ) $)
	bl.sbwsyl.2  $( |- ( ch <-> th ) $)
	$( wffs for pm2.86i $)
	  wch wth wb  $( ph= ( ch <-> th ) $)
	  wph  $( ps= ph $)
	  wps  $( ch= ps $)
	$( wffs for 3imtr3i $)
	  wph wth wch wsbw  $( ph= [- th / ch ]- ph $)
	  wps wth wch wsbw  $( ps= [- th / ch ]- ps $)
	  wch wth wb wph wi  $( ch= ( ( ch <-> th ) -> ph ) $)
	  wch wth wb wps wi  $( th= ( ( ch <-> th ) -> ps ) $)
	bl.sbwsyl.1 $( |- ( [- th / ch ]- ph -> [- th / ch ]- ps ) $)
	$( using df-bl.sbw  with ph= ph  and  ps= th  and ch= ch
		make  B:  |- ( [- th / ch ]- ph <-> ( ( ch <-> th ) -> ph ) ) $)
	  wph wth wch
	df-bl.sbw
	$( using df-bl.sbw  with ph= ph  and  ps= th  and ch= ch
		make C: |- ( [- th / ch ]- ps <-> ( ( ch <-> th ) -> ps ) ) $)
	  wps wth wch
	df-bl.sbw
	$( by 3imtr3i with ph= [- th / ch ]- ph  and  ps= [- th / ch ]- ps 
		ch= ( ( ch <-> th ) -> ph )  and  th= ( ( ch <-> th ) -> ps ) 
		to make |- ( ( ( ch <-> th ) -> ph ) -> ( ( ch <-> th ) -> ps ) )  $)
	3imtr3i
	$( use pm2.86i with ph= ( ch <-> th )  and  ps= ph  and  ch= ps
		to make |- ( ( ch <-> th ) -> ( ph -> ps ) )  $)
	pm2.86i	
	ax-mp
	$( |- ( ph -> ps ) $)
	$.
$}
$( end of bl.sbwsyl $)
$( this theorem also was verified on first draft;  two-in-a-row  brl 4/1/2011  $)


  
$( 
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#
Well-formed formula list
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#

BLESS has no limit on the number of terms for ` /\ ` or ` \/ `  so 
equivlant constructs were created using lists of wffs.

Caution:  Although theorems can be proved using MM-PA with more than 3 wffs in a
list, mmj2 unification will fail.  There are several additional theorems using wff
lists which are not included in set.mm for this reason.
$)

$( make wff-list variables ` l_ l2 l3 ` $)
$v l_ l2 l3 $.  
$( declare ` l_ ` to be a lw  $)
wl1 $f lw l_ $. 
$( declare ` l2 ` to be a lw  $)
wl2 $f lw l2 $. 
$( declare ` l3 ` to be a lw  $)
wl3 $f lw l3 $. 

$( WFF-list:  one wff $)
wfl1 $a lw ph $. 

$(  WFF-list: two-element  $)
wfl2 $a lw l_ l2 $. 

$(  WFF-list: three-element  $)
$( wfl3 $a lw l_ l2 l3 $. $)

$( Multiterm And:  define conjunction of a list of WFF $)
wland $a wff /\( l_ )x $.

$( Multiterm Or:  define disjunction of a list of WFF $)
wlo $a wff \/( l_ )x $.


$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Conjunction using well-formed formula lists:  ` /\( l_ l2 )x `
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Conjunction of one WFF-list. $)
df-bl.lan1 $a |- ( /\( ph )x <-> ph ) $. 

$( Conjunction of two WFF-lists. $)
df-bl.lan2wl $a |- ( /\( l_ l2 )x <-> ( /\( l_ )x /\ /\( l2 )x ) ) $.

$( Conjunction of two WFF. $)
bl.an2wl $p |- ( /\( ph ps )x <-> ( ph /\ ps ) )
   $= ( wfl1 wfl2 wland wa df-bl.lan2wl df-bl.lan1 anbi12i bitri ) 
   ACZBCZDEKEZLEZFABFKLGMANBAHBHIJ $.
	
$( Conjunction of three WFF. $)
bl.an3wl $p |- ( /\( ph ps ch )x <-> ( ph /\ ps /\ ch ) )
  $= ( wfl1 wfl2 wland wa df-bl.lan2wl df-bl.lan1 bl.an2wl anbi12i
  bitri w3a 3anass bitr4i ) 
  ADZBDCDEZEFZABCGZGZABCMRPFZQFZGTPQHUAAUBSAIBCJKLABCNO $.

$( Move first WFF to end of conjunction WFF-list. $)
bl.ancomphwl $p |- ( /\( ph l_ )x <-> /\( l_ ph )x )
  $= ( wfl1 wfl2 wland wa df-bl.lan2wl df-bl.lan1 anbi2i anbi1i
  3bitr4ri ancom bitri bitr2i ) 
  BACZDEBEZOEZFZOBDEZBOGRPAFZSQAPAHZIQPFAPFSTQAPUAJOBGPALKMN $.

$( Commute conjunction of two WFF-lists. $)
bl.ancomwlwl $p |- ( /\( l_ l2 )x <-> /\( l2 l_ )x )
  $= ( wland wa wfl2 ancom df-bl.lan2wl 3bitr4i ) 
  ACZBCZDJIDABECBAECIJFABGBAGH $.

$( Pull first WFF from conjunction WFF-list. $)
bl.anpfw $p |- ( /\( ph l_ )x <-> ( ph /\ /\( l_ )x ) )
  $= ( wfl1 wfl2 wland wa df-bl.lan2wl df-bl.lan1 anbi1i bitri ) 
  ACZBDEKEZBEZFAMFKBGLAMAHIJ $.

$( Pull last WFF from conjunction WFF-list. $)
bl.anplw $p |- ( /\( l_ ph )x <-> ( /\( l_ )x /\ ph ) )
  $= ( wfl1 wfl2 wland wa df-bl.lan2wl df-bl.lan1 anbi2i bitri ) 
  BACZDEBEZKEZFLAFBKGMALAHIJ $.


$( Absorb first term conjunction WFF-list. $)
bl.anabpf $p |- ( /\( /\( l_ )x l2 )x <-> /\( l_ l2 )x )
  $= ( wland wfl1 wfl2 wa df-bl.lan2wl df-bl.lan1 anbi1i bitr4i ) 
  ACZDZBECLCZBCZFZABECZLBGPKNFOABGMKNKHIJJ $.

$( Absorb last term conjunction WFF-list.  $)
bl.anabpl $p |- ( /\( l_ /\( l2 )x )x <-> /\( l_ l2 )x )
  $= ( wland wfl1 wa wfl2 df-bl.lan1 anbi2i df-bl.lan2wl 3bitr4i ) 
  ACZBCZDZCZEKLEAMFCABFCNLKLGHAMIABIJ $.
     
$(  And-Introduction Schema of WFF (left). $)
bl.aisl $p |-  ( /\( l_ ph )x -> ph )
$=  ( wfl1 wfl2 wland wa bl.anplw simpr sylbi ) BACDEBEZAFAABGJAHI $.       
   $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.aisl $)   
     
$(  And-Introduction Schema of WFF (right). $)
bl.aisr $p  |- ( /\( ph l_ )x -> ph )
$=  ( wfl1 wfl2 wland wa bl.anpfw simpl sylbi ) ACBDEABEZFAABGAJHI $.     
   $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.aisr $)   
     
$(  And-Introduction Schema of WFF-list (left). $)
bl.aiswll $p |- ( /\( l_ l2 )x -> /\( l2 )x ) 
$=  ( wfl2 wland wa df-bl.lan2wl simpr sylbi ) ABCDADZBDZEJABFIJGH $.     
    $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.aiswll $)   
    
$(  And-Introduction Schema of WFF-list (right). $)
bl.aiswlr $p  |- ( /\( l_ l2 )x -> /\( l_ )x )
$=  ( wfl2 wland wa df-bl.lan2wl simpl sylbi ) ABCDADZBDZEIABFIJGH $.     
    $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.aiswlr $)   

$( bl.ancomphfirst bl.ancomphlast bl.anpmw bl.anabpm bl.ais and bl.aiswl won't unify 
by mmj2.  They are in bless.mm which calls set.mm  $)


$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Disjunction using well-formed formula lists:  ` \/( l_ l2 )x `
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Disjunction of one WFF-list. $)
df-bl.lor1 $a |- ( \/( ph )x <-> ph ) $.

$( Disjunction of two WFF-lists. $)
df-bl.lor2wl $a |- ( \/( l_ l2 )x <-> ( \/( l_ )x \/ \/( l2 )x ) ) $.

$( Disjunction of two WFF. $)
bl.or2wl $p |- ( \/( ph ps )x <-> ( ph \/ ps ) )
  $= ( wfl1 wfl2 wlo wo df-bl.lor2wl df-bl.lor1 orbi12i bitri ) 
  ACZBCZDEKEZLEZFABFKLGMANBAHBHIJ $.

$( Disjunction of three WFF. $)
bl.or3wl $p |- ( \/( ph ps ch )x <-> ( ph \/ ps \/ ch ) )
  $= ( wfl1 wfl2 wlo wo w3o df-bl.lor2wl df-3or orbi1i bitr4i df-bl.lor1 3orbi123i bitr3i bitri ) 
  ADZBDZCDZEEFQREZFZSFZGZABCHZTSIUCQFZRFZUBHZUDUGUEUFGZUBGUCUEUFUBJUAUHUBQRIKLUEAUFBUBCAMBMCMNOP $.

$( Move first WFF to end of disjunction WFF-list. $)
bl.orcomphwl $p |- ( \/( ph l_ )x <-> \/( l_ ph )x )
  $= ( wfl1 wlo wo wfl2 orcom df-bl.lor2wl 3bitr4i ) 
  ACZDZBDZELKEJBFDBJFDKLGJBHBJHI $.

$( Disjunction Commutes. $)
bl.orcom $p |- ( \/( l_ l2 )x <-> \/( l2 l_ )x )
  $= ( wlo wo wfl2 orcom df-bl.lor2wl 3bitr4i ) 
  ACZBCZDJIDABECBAECIJFABGBAGH $.

$( Pull first WFF from disjunction WFF-list. $)
bl.orpfw $p |- ( \/( ph l_ )x <-> ( ph \/ \/( l_ )x ) )
  $= ( wfl1 wfl2 wlo wo df-bl.lor2wl df-bl.lor1 orbi1i bitri ) 
  ACZBDEKEZBEZFAMFKBGLAMAHIJ $.

$( Pull last WFF from disjunction WFF-list. $)
bl.orplw $p |- ( \/( l_ ph )x <-> ( \/( l_ )x \/ ph ) )
  $= ( wfl1 wfl2 wlo wo df-bl.lor2wl df-bl.lor1 orbi2i bitri ) 
  BACZDEBEZKEZFLAFBKGMALAHIJ $.

$( Absorb first term disjunction WFF-list. $)
bl.orabpf $p |- ( \/( \/( l_ )x l2 )x <-> \/( l_ l2 )x )
  $= ( wlo wfl1 wo wfl2 df-bl.lor1 orbi1i df-bl.lor2wl 3bitr4i ) 
  ACZDZCZBCZEKNELBFCABFCMKNKGHLBIABIJ $.


$( Absorb last term disjunction WFF-list. $)
bl.orabpl $p |- ( \/( l_ \/( l2 )x )x <-> \/( l_ l2 )x )
  $= ( wlo wfl1 wo wfl2 df-bl.lor1 orbi2i df-bl.lor2wl 3bitr4i ) 
  ACZBCZDZCZEKLEAMFCABFCNLKLGHAMIABIJ $.
    
$(  Or-Introduction Schema of WFF (right). $)
bl.orcwl $p  |- ( ph -> \/( l_ ph )x )
$=  ( wlo wo wfl1 wfl2 olc bl.orplw sylibr ) ABCZADBAEFCAJGABHI $.    
    $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.orcwl $)   
     
$(  Or-Introduction Schema of WFF (left). $)
bl.orcwll $p  |- ( ph -> \/( ph l_ )x )
$=  ( wlo wo wfl1 wfl2 orc bl.orpfw sylibr ) AABCZDAEBFCAJGABHI $.      
    $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.orcwll $)   
      
$( bl.orcomphfirst bl.orcomphlast bl.orpmw and bl.orabpm won't unify by mmj2, either  $)

$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Combined conjunction and disjunction using well-formed formula lists
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$( Distribution or-over-and two terms with WFF-lists.  $)
bl.dbo2a $p  |- ( /\( l_ ( ph \/ ps ) )x <-> 
		( ( ph /\ /\( l_ )x ) \/ ( ps /\ /\( l_ )x ) ) )
$=  ( wo wfl1 wfl2 wland wa bl.ancomwlwl df-bl.lan2wl bitri anbi1i andir
    df-bl.lan1 3bitri ) CABDZEZFGZQGZCGZHZPTHATHBTHDRQCFGUACQIQCJKSPTPNL
    ABTMO $.
   $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.dba2a $)   

$( Distribution and-over-or two terms with WFF-lists.  $)
bl.dba2o $p |- ( \/( l_ ( ph /\ ps ) )x <-> 
		( ( ph \/ \/( l_ )x ) /\ ( ps \/ \/( l_ )x ) ) )
$=  ( wa wfl1 wfl2 wlo wo bl.orcom df-bl.lor2wl bitri df-bl.lor1 orbi1i
    ordir 3bitri ) CABDZEZFGZQGZCGZHZPTHATHBTHDRQCFGUACQIQCJKSPTPLMAB
    TNO $.
   $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.dba2o $)   
    
$( Distribution or-over-and with WFF-lists. $)
bl.dbo2awl $p |- ( /\( l_ \/( l2 l3 )x )x <-> 
	( ( \/( l2 )x /\ /\( l_ )x ) \/ ( \/( l3 )x /\ /\( l_ )x ) ) )
$=  ( wfl2 wfl1 wland wa wo wb bl.anplw ancom bibi2i df-bl.lor2wl anbi1i
    wlo mpbi andir 3bitri ) ABCDOZEDFZSAFZGZBOZCOZHZUAGUCUAGUDUAGHTUA
    SGZITUBISAJUFUBTUASKLPSUEUABCMNUCUDUAQR $.     
   $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.dbo2awl $)   
    
$( Distribution and-over-or with WFF-lists. $)
bl.dba2owl $p |- ( \/( l_ /\( l2 l3 )x )x <-> 
		( ( /\( l2 )x \/ \/( l_ )x ) 
		/\ ( /\( l3 )x \/ \/( l_ )x ) ) )
$=  ( wfl2 wland wfl1 wo wa wb bl.orplw orcom bibi2i df-bl.lan2wl orbi1i
    wlo mpbi ordir 3bitri ) ABCDEZFDOZSAOZGZBEZCEZHZUAGUCUAGUDUAGHTUA
    SGZITUBISAJUFUBTUASKLPSUEUABCMNUCUDUAQR $.		
   $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.dba2owl $)   


$(  Common Term Between And-List and Or-List (right). $)
bl.ctao $p |- ( /\( l_ ph )x -> \/( l2 ph )x ) 
$=  ( wland wa wlo wo wfl1 wfl2 animorr bl.anplw bl.orplw 3imtr4i ) B
    DZAECFZAGBAHZIDCPIFNAOJABKACLM $.
   $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.ctao $)   

$(  Common Term Between And-List and Or-List (left). $)
bl.ctaol $p   |- ( /\( ph l_ )x -> \/( ph l2 )x )
$=  ( wland wa wlo wo wfl1 wfl2 animorl bl.anpfw bl.orpfw 3imtr4i ) A
    BDZEACFZGAHZBIDPCIFANOJABKACLM $.
    $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.ctaol $)   
   
$( 	Premise Has All Terms of Conjunction Within Disjunction (right). $)
bl.animporan $p  |-  ( /\( l_ l2 )x -> \/( l3 /\( l2 )x )x )
$=  ( wfl2 wland wlo wo wfl1 df-bl.lan2wl animorr sylbi bl.orplw sylibr
    wa ) ABDEZCFZBEZGZCQHDFOAEZQNRABISQPJKQCLM $.    
    $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.animporan $)   
    
$( 	Premise Has All Terms of Conjunction Within Disjunction (left). $)
bl.animporanl $p |- ( /\( l2 l_ )x -> \/( /\( l2 )x l3 )x )
$=  ( wland wa wlo wo wfl2 wfl1 animorl df-bl.lan2wl bl.orpfw 3imtr4i )
    BDZADZENCFZGBAHDNICHFNOPJBAKNCLM $.    
    $( [brl] $) $( [09-Sep-2021] $)
$( end of bl.animporanl $)   
     

    
$( 
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#
  Class list
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#

In Metamath, function application is defined as (F`A) where F is a class
function applied to class A.  Unfortuntely, ordered pairs <. A , B >. and 
triples <. A , B , C .> are defined, but not arbitray n-tuples.
Here we define a class that is a n-tuple of set variables.
Visually, the same angle brackets will be used, but internally <.. and ..> 
are used to keep the single df- policy. 

$)

$( a clist is comma separated class variables. $)
bl.cl1 $f bcl cl_1 $. 
bl.cl2 $f bcl cl_2 $. 

$( A single Class is a Classlist. $)
bl.cla $a bcl A $.  

$( A Classlist followed by a comma and a Class is a Classlist. $)
bl.cln $a bcl cl_1 , cl_2  $. 

$( Make a Classlist into a Class. $)
df-bl.cl $a class <.. cl_1 >.. $. 

$( Allow 0-Tuple. $)
df-bl.cl0 $a class <.. >.. $.

$(  Correspondence of 2-Tuple to Ordered Pair. $)
df-bl.2teqop $a |- <.. A , B >.. = <. A , B >. $. 

$(  Correspondence of a 3-Tuple to Ordered Triple. $)
df-bl.3teqot $a |- <.. A , B , C >.. = <. A , B , C >. $.

$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Addition and multitplicattion using class lists
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$( Multiterm Addition is a Class. $)
bl.cadd $a class +( cl_1 )x $.

$( Multiterm Addition of Single Value is that Value. $)
df-bl.add1 $a |- ( A e. RR -> +( A )x = A ) $.

$( Multiterm Addition of Two Class Lists is their Sum. $) 
df-bl.add2 $a |- +( cl_1 , cl_2 )x = ( +( cl_1 )x + +( cl_2 )x ) $.

$( Multiterm Addition Commutes. $) 
bl.addcom $p |- +( cl_1 , cl_2 )x = +( cl_2 , cl_1 )x 
$= ( bl.cadd caddc co bl.cln addcomgi df-bl.add2 3eqtr4i ) ACZBCZDEKJ
  DEABFCBAFCJKGABHBAHI $.

${
bl.adeqi.1 $e |- A = B $.
bl.adeqi.2 $e |- C = D $.
$( Adding Equals. $)
bl.adeqi $p |- ( A + C ) = ( B + D )
  $= ( caddc oveq12i ) ABCDGEFH $.
$}

${
bl.add2i.1 $e |- A e. RR $.
bl.add2i.2 $e |- B e. RR $.
$( Multiterm Addition of Two Values Lists is their Sum. $) 
bl.add2i $p |- +( A , B )x = ( A + B ) 
  $= ( bl.cla bl.cln bl.cadd caddc co df-bl.add2 cr wcel wceq
  df-bl.add1 ax-mp bl.adeqi eqtri ) AEZBEZFGRGZSGZHIABHIRSJTAUABAKLTA
  MCANOBKLUABMDBNOPQ $.
$}

${
bl.add3i.1 $e |- A e. RR $.
bl.add3i.2 $e |- B e. RR $.
bl.add3i.3 $e |- C e. RR $.
$( Multiterm Addition of Three Values. $)
bl.add3i $p |- +( A , B , C )x = ( A + ( B + C ) ) 
  $= ( bl.cla bl.cln bl.cadd caddc co df-bl.add2 cr wcel wceq
  df-bl.add1 ax-mp bl.add2i bl.adeqi eqtri ) AGZBGCGHZHIUAIZUBIZJKABC
  JKZJKUAUBLUCAUDUEAMNUCAODAPQBCEFRST $.
$}

$(
${
bl.add4i.1 $e |- A e. RR $.
bl.add4i.2 $e |- B e. RR $.
bl.add4i.3 $e |- C e. RR $.
bl.add4i.4 $e |- D e. RR $.
$)
$( Multiterm Addition of Four Values. $)
$(
bl.add4i $p |- +( A , B , C , D )x = ( ( A + B ) + ( C + D ) ) 
  $= 
  cA bl.cla cB bl.cla cC bl.cla cD bl.cla bl.cln bl.cln bl.cln bl.cadd cA
  bl.cla cB bl.cla bl.cln bl.cadd cC bl.cla cD bl.cla bl.cln bl.cadd caddc co
  cA cB caddc co cC cD caddc co caddc co cA bl.cla cB bl.cla bl.cln cC bl.cla
  cD bl.cla bl.cln df-bl.add2 cA bl.cla cB bl.cla bl.cln bl.cadd cA cB caddc co
  cC bl.cla cD bl.cla bl.cln bl.cadd cC cD caddc co cA cB bl.add4i.1 bl.add4i.2
  bl.add2i cC cD bl.add4i.3 bl.add4i.4 bl.add2i bl.adeqi eqtri $.
$}
$)

$( Addition Two Values Commutes. $)
bl.addcom2 $p |- +( A , B )x = +( B , A )x
$= ( bl.cla bl.addcom ) ACBCD $.

${
bl.addcom3bac.1 $e |- A e. RR $.
bl.addcom3bac.2 $e |- B e. RR $.
bl.addcom3bac.3 $e |- C e. RR $.
$( Addition of Three Values Commutes. $)
bl.addcom3bac $p |- +( A , B , C )x = +( B , A , C )x
$= ( caddc co bl.cla bl.cln bl.cadd cc wcel w3a wceq recni add12
  ax-mp 3pm3.2i bl.add3i 3eqtr4i ) ABCGHGHZBACGHGHZAIZBIZCIZJJKUEUDUF
  JJKALMZBLMZCLMZNUBUCOUGUHUIADPBEPCFPSABCQRABCDEFTBACEDFTUA $.
$}

${
bl.addcom3acb.1 $e |- A e. RR $.
bl.addcom3acb.2 $e |- B e. RR $.
bl.addcom3acb.3 $e |- C e. RR $.
$( Addition of Three Values Commutes. $)
bl.addcom3acb $p |- +( A , B , C )x = +( A , C , B )x
$= ( caddc co bl.cla bl.cln bl.cadd addcomgi oveq2i bl.add3i 3eqtr4i
  ) ABCGHZGHACBGHZGHAIZBIZCIZJJKRTSJJKPQAGBCLMABCDEFNACBDFENO $.
$}

${
  bl.addcom3cba.1 $e |- A e. RR $.
  bl.addcom3cba.2 $e |- B e. RR $.
  bl.addcom3cba.3 $e |- C e. RR $.
$( Addition of Three Values Commutes. $)
bl.addcom3cba $p |- +( A , B , C )x = +( C , B , A )x
  $= ( caddc bl.cla bl.cln bl.cadd addcomgi bl.add3i recni eqtr4i
  oveq1i co addassi eqtri 3eqtr4i ) BAGPZCGPZCTGPAHZBHZCHZIIJZUDUCUBI
  IJTCKUEABGPZCGPZUAUEABCGPGPUGABCDEFLABCADMBEMCFMQNUFTCGABKORCBAFEDL
  S $.
$}

${
  bl.addcom3cab.1 $e |- A e. RR $.
  bl.addcom3cab.2 $e |- B e. RR $.
  bl.addcom3cab.3 $e |- C e. RR $.
$( Addition of Three Values Commutes. $)
bl.addcom3cab $p |- +( A , B , C )x = +( C , A , B )x
  $= ( co bl.cla bl.cln bl.cadd addcomgi bl.add3i addassi eqtr4i
  3eqtr4i caddc recni ) ABPGZCPGZCRPGAHZBHZCHZIIJZUBTUAIIJRCKUCABCPGP
  GSABCDEFLABCADQBEQCFQMNCABFDELO $.
$}

$( Multiterm Multiplication is a Class. $)
bl.cmul $a class *( cl_1 )x $.

$( Multiterm Multiplication of Single Value is that Value. $)
df-bl.mul1 $a |- ( A e. RR -> *( A )x = A ) $.


$( Multiterm Multiplication of Two Class Lists is their Product. $) 
df-bl.mul2 $a |- *( cl_1 , cl_2 )x = ( *( cl_1 )x x. *( cl_2 )x ) $.

${
  bl.mulcom.1 $e |- *( cl_1 )x e. RR $.
  bl.mulcom.2 $e |- *( cl_2 )x e. RR $.
$( Multiterm Multiplication Commutes. $) 
bl.mulcom $p |- *( cl_1 , cl_2 )x = *( cl_2 , cl_1 )x 
  $= ( bl.cmul cmul co bl.cln recni mulcomi df-bl.mul2 3eqtr4i ) AEZBEZ
  FGNMFGABHEBAHEMNMCINDIJABKBAKL $.
$}

${
bl.muleqi.1 $e |- A = B $.
bl.muleqi.2 $e |- C = D $.
$( Multiplying Equals. $)
bl.muleqi $p |- ( A x. C ) = ( B x. D )
  $= ( cmul oveq12i ) ABCDGEFH $.
$}

${
  bl.mul2i.1 $e |- A e. RR $.
  bl.mul2i.2 $e |- B e. RR $.
$( Multiterm Multiplication of Two Values is their Product. $) 
bl.mul2i $p |- *( A , B )x = ( A x. B ) 
  $= ( bl.cla bl.cln bl.cmul cmul co df-bl.mul2 cr wcel df-bl.mul1
  ax-mp wceq oveq12i eqtri ) AEZBEZFGRGZSGZHIABHIRSJTAUABHAKLTAOCAMNB
  KLUABODBMNPQ $.
$}


${
  bl.mul3i.1 $e |- A e. RR $.
  bl.mul3i.2 $e |- B e. RR $.
  bl.mul3i.3 $e |- C e. RR $.
$( Multiterm Multiplication of Three Values. $)
bl.mul3i $p |- *( A , B , C )x = ( A x. ( B x. C ) ) 
  $= ( bl.cla bl.cln bl.cmul cmul co df-bl.mul2 cr wcel df-bl.mul1
  ax-mp wceq oveq12i eqtri ) AGZBGZCGZHZHITIZUCIZJKABCJKZJKTUCLUDAUEU
  FJAMNUDAQDAOPUEUAIZUBIZJKUFUAUBLUGBUHCJBMNUGBQEBOPCMNUHCQFCOPRSRS
  $.
$}

$(
${
bl.mul4i.1 $e |- A e. CC $.
bl.mul4i.2 $e |- B e. CC $.
bl.mul4i.3 $e |- C e. CC $.
bl.mul4i.4 $e |- D e. CC $.
$)
$( Multiterm Multiplication of Four Values. $)
$(
bl.mul4i $p |- *( A , B , C , D )x = ( ( A x. B ) x. ( C x. D ) ) 
  $= 
  cA bl.cla cB bl.cla cC bl.cla cD bl.cla bl.cln bl.cln bl.cln bl.cmul cA
  bl.cla cB bl.cla bl.cln bl.cmul cC bl.cla cD bl.cla bl.cln bl.cmul cmul co cA
  cB cmul co cC cD cmul co cmul co cA bl.cla cB bl.cla bl.cln cC bl.cla cD
  bl.cla bl.cln df-bl.mul2 cA bl.cla cB bl.cla bl.cln bl.cmul cA cB cmul co cC
  bl.cla cD bl.cla bl.cln bl.cmul cC cD cmul co cA cB bl.mul4i.1 bl.mul4i.2
  bl.mul2i cC cD bl.mul4i.3 bl.mul4i.4 bl.mul2i bl.muleqi eqtri $.
$}
$)

${
  bl.mulcom2.1 $e |- A e. RR $.
  bl.mulcom2.2 $e |- B e. RR $.
$( Multiplication of Two Values Commutes. $)
bl.mulcom2 $p |- *( A , B )x = *( B , A )x
  $= ( bl.cla bl.cmul cr wcel wceq df-bl.mul1 ax-mp eqeltri bl.mulcom )
  AEZBEZNFZAGAGHPAICAJKCLOFZBGBGHQBIDBJKDLM $.
$}

${
  bl.mulcom3bac.1 $e |- A e. RR $.
  bl.mulcom3bac.2 $e |- B e. RR $.
  bl.mulcom3bac.3 $e |- C e. RR $.
$( Multiplication of Three Values Commutes. $)
bl.mulcom3bac $p |- *( A , B , C )x = *( B , A , C )x
  $= ( cmul co bl.cla bl.cln bl.cmul recni mul12i bl.mul3i 3eqtr4i ) AB
  CGHGHBACGHGHAIZBIZCIZJJKQPRJJKABCADLBELCFLMABCDEFNBACEDFNO $.
$}

${
  bl.mulcom3acb.1 $e |- A e. RR $.
  bl.mulcom3acb.2 $e |- B e. RR $.
  bl.mulcom3acb.3 $e |- C e. RR $.
$( Multiplication of Three Values Commutes. $)
bl.mulcom3acb $p |- *( A , B , C )x = *( A , C , B )x
  $= ( cmul bl.cla bl.cln bl.cmul recni mulcomi oveq2i bl.mul3i 3eqtr4i
  co ) ABCGPZGPACBGPZGPAHZBHZCHZIIJSUATIIJQRAGBCBEKCFKLMABCDEFNACBDFE
  NO $.
$}

${
  bl.mulcom3cba.1 $e |- A e. RR $.
  bl.mulcom3cba.2 $e |- B e. RR $.
  bl.mulcom3cba.3 $e |- C e. RR $.
$( Multiplication of Three Values Commutes. $)
bl.mulcom3cba $p |- *( A , B , C )x = *( C , B , A )x
  $= ( cmul co bl.cla bl.cln bl.cmul cc wcel recni ax-mp bl.mul3i
  pm3.2i wceq wa mulcom w3a 3pm3.2i mulass mulcl oveq1i eqtr4i
  3eqtr4i eqtri ) CBGHZAGHZCBAGHGHZAIZBIZCIZJJKZUNUMULJJKCLMZBLMZALMZ
  UAUJUKRUPUQURCFNZBENZADNZUBCBAUCOUOBCGHZAGHZUJUOAVBGHZVCABCDEFPURVB
  LMZSVDVCRURVEVAUQUPSVEUQUPUTUSQBCUDOQAVBTOUHUIVBAGUPUQSUIVBRUPUQUSU
  TQCBTOUEUFCBAFEDPUG $.
$}

${
  bl.mulcom3cab.1 $e |- A e. RR $.
  bl.mulcom3cab.2 $e |- B e. RR $.
  bl.mulcom3cab.3 $e |- C e. RR $.
$( Multiplication of Three Values Commutes. $)
  bl.mulcom3cab $p |- *( A , B , C )x = *( C , A , B )x
  $= ( cmul co bl.cla bl.cln bl.cmul cc wcel wceq recni 3pm3.2i
  mulass w3a ax-mp bl.mul3i wa mulcli pm3.2i mulcom eqtr3i
  3eqtr4i ) ABCGHGHZCABGHZGHZAIZBIZCIZJJKULUJUKJJKUHCGHZUGUIALMZBLMZC
  LMZRUMUGNUNUOUPADOZBEOZCFOZPABCQSUHLMZUPUAUMUINUTUPABUQURUBUSUCUHCU
  DSUEABCDEFTCABFDETUF $.
$}

$( 
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#
  BLESS Logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#**#*#*#*#*#*#*#*#

BLESS Logic is first-order predicate calculus augmented with an operator
specifying *when* an expression or predicate should be evaluated.

BLESS Logic is a modal logic defined as a Kripke tuple.  Other "worlds" are
accessed through a temporal operator: @

p@t means evaluate p at time t.

Here the model constructed by execution is ` mathfrakM ` over a set of time 
instants ` TIME ` with temporal precidence operator ` b~< `.  Thus the temporal
frame for BLESS Logic is ` <. TIME , b~<= >. `  

Only variables in ` VAR ` have different values depening on which world they're 
evaluated.

Set-variable symbols are introduced for those values corresponding to instants in
` TIME ` for which a world exists to evaluate p@t.
$)


$( time values $)
vt0 $f class t_0  $. 
vt1 $f class t_1  $.
vt2 $f class t_2   $.
vt3 $f class t_3   $.
vtr $f class t_r   $.

$( now, tops and TIME must use $a because they are constants! $)
$( ` now ` is a class. $)
cnow $a class now $.
$( tops is a class. $)
ctops $a class tops $.
$( ` TIME ` is a class. $)
ctime $a class TIME $. 

$(  ***** TIME *****  $)

$( Define domain of time ` TIME ` from ` t = 0 ` to ` now `. $)
df-bl.time $a |- TIME = { x | ( x e. RR /\ 0 <_ x /\ x <_ now ) }   $.    

$( ` TIME ` is ` RR ` (real) $)
bl.rt $p |- TIME C_ RR 
  $= ( vx ctime cr wcel cc0 cle wbr cnow w3a cab df-bl.time eleq2i
  bitri cv abid simp1bi ssriv ) ABCANZBDZRCDZERFGZRHFGZSRTUAUBIZAJZDU
  CBUDRAKLUCAOMPQ $.

$( ` TIME ` is ` RR `* (extended real) $)
bl.ert $p |- TIME C_ RR* 
  $= ( ctime cr cxr bl.rt ressxr sstri ) ABCDEF $.

$( Every time is real $)
bl.etir $p |- ( t_1 e. TIME -> t_1 e. RR )
  $= ( ctime cr bl.rt sseli ) BCADE $.

  ${
  $d t_1 x $.  
$( Every time is at least 0. $)
bl.etial0 $p |- ( t_1 e. TIME -> 0 <_ t_1  )  
  $= ( vx ctime wcel cc0 cv csb cle wbr wsbc cr cnow w3a cab wceq wa
  wex clelab df-bl.time mpbid eleq2i 3bitr4i sbc3an bitri simp2bi
  sbcbr2g sbc5 eqidd csbvarg breq12d ) ACDZEBABFZGZHIZEAHIUKEULHIZBAJ
  ZUNUKULKDZBAJZUPULLHIZBAJZUKUQUOUSMZBAJZURUPUTMAVABNZDULAOVAPBQUKVB
  VABARCVCABSUAVABAUGUBUQUOUSBAUCUDUEBAEULHCUFTUKEEUMAHUKEUHBACUIUJT
  $.
  $}
  
  ${
  $d t_1 x $.  
$( Every time is at most now. $)
bl.etiamn $p |- ( t_1 e. TIME -> t_1 <_ now )  
  $= ( vx ctime wcel cv csb cnow cle csbvarg wbr wsbc cr cc0 w3a wceq
  wa cab wex clelab df-bl.time eleq2i sbc5 3bitr4i bitri simp3bi
  sbcbr1g sbc3an mpbid eqbrtrrd ) ACDZBABEZFZAGHBACIUJUKGHJZBAKZULGHJ
  UJUKLDZBAKZMUKHJZBAKZUNUJUOUQUMNZBAKZUPURUNNAUSBQZDUKAOUSPBRUJUTUSB
  ASCVAABTUAUSBAUBUCUOUQUMBAUGUDUEBAUKGHCUFUHUI $.
  $}

$( Temporal Precedence, before $)
wtp $a wff t_1 b~< t_2 $.
$( Temporal Precedence, before or coincident $)
wtpe $a wff t_1 b~<= t_2 $.

$( b~< respects equality of its left argument (Leibniz congruence).  Not
   derivable from df-bl.before alone, since that only pins down b~<'s
   behavior when both arguments are in TIME; asserted directly, matching
   how breq1/breq2 give this "for free" to wbr-based relations like <,
   which b~< is not (it is its own primitive wff, not built via wbr). $)
bl.tpeq1 $a |- ( A = B -> ( A b~< C <-> B b~< C ) ) $.

$( b~< respects equality of its right argument (Leibniz congruence). $)
bl.tpeq2 $a |- ( A = B -> ( C b~< A <-> C b~< B ) ) $.

$( Temporal Precedence (before). $)
df-bl.before $a |- ( ( t_1 e. TIME /\ t_2 e. TIME ) -> 
		( t_1 b~< t_2 <-> t_1 < t_2 ) ) $.   

$( Temporal Precedence (before or coincident). $)
df-bl.beforeeq $a |- ( ( t_1 e. TIME /\ t_2 e. TIME ) -> 
		 ( t_1 b~<= t_2 <-> ( t_1 < t_2 \/ t_1 = t_2 ) ) ) $.


$( Temporal Precedence (before or coincident) $)
$( bl.beforeeq $p |-  ( ( t_1 e. TIME /\ t_2 e. TIME ) -> 
		( t_1 b~<= t_2 <-> t_1 <_ t_2 ) )
  $= ( ctime wcel wa wtpe clt wbr wceq wo df-bl.beforeeq bl.etir
  anim12i cle cr wb leloe syl bitr4d ) ACDZBCDZEZABFABGHABIJZABNHZABK
  UBAODZBODZEUDUCPTUEUAUFALBLMABQRS $.  
$)

$(  ***** now *****  $)

$( now is a non-negative real number. $)
df-bl.nowrr $a |- ( now e. RR /\ 0 <_ now ) $.

$( now is a time ` now e. TIME `  $)
bl.nowt $p |- now e. TIME
  $= ( vx cnow ctime wcel cv cr cc0 cle wbr w3a df-bl.nowrr simpli
  mpbir wsbc wb ax-mp eqid wceq breq12i bitri sbcel1v simpri csb
  sbcbr2g wa csbvarg leid sbcbr1g 3pm3.2i cab wex clelab df-bl.time
  sbc5 3bitr4i eleq2i sbc3an ) BCDZAEZFDZABNZGUSHIZABNZUSBHIZABNZJZVA
  VCVEVABFDZVGGBHIZKLZABFUAMVCVHVGVHKUBVCGABUSUCZHIZVHVGVCVKOVIABGUSH
  FUDPGGVJBHGQVGVJBRVIABFUFPZSTMVEVJBHIZVMBBHIZVGVNVIBUGPVJBBBHVLBQSM
  VGVEVMOVIABUSBHFUHPMUIURUTVBVDJZABNZVFBVOAUJZDUSBRVOUEAUKURVPVOABUL
  CVQBAUMUPVOABUNUOUTVBVDABUQTM $.
  
$(  ***** Temporal Intervals *****  $)

${
  bl.alldd.1 $e |- ( t_1 e. TIME /\ t_2 e. TIME ) $.
$( Universal quantification over closed time interval [t1 .. t2]. $)
bl.alldd $p |- (  A. x e. TIME ( x e. ( t_1 [,] t_2 ) /\ ph )  <-> 
  A. x e. TIME ( t_1 <_ x /\ x <_ t_2 /\ ph ) ) 
  $= ( cv cicc wcel ctime wral cxr cle wbr w3a ax-mp bl.ert sseli
  bitr4i wa bitri co wb simpl simpr pm3.2i elicc1 3anass anbi1i anass
  df-3an anbi2i ralbii bl.ralssi ) BFZCDGUAHZASZBIJUNKHZCUNLMZUNDLMZA
  NZSZBIJUTBIJUPVABIUPUQURUSSZASZSZVAUPUQVBSZASVDUOVEAUOUQURUSNZVECKH
  ZDKHZSUOVFUBVGVHCIHZVGVIDIHZSZVIEVIVJUCOIKCPQOVJVHVKVJEVIVJUDOIKDPQ
  OUECDUNUFOUQURUSUGTUHUQVBAUITUTVCUQURUSAUJUKRULUTBIKPUMR $.
$}

${
  bl.allcd.1 $e |- ( t_1 e. TIME /\ t_2 e. TIME ) $.
$( Universal quantification over open-left time interval [t1 ,. t2]. $)
bl.allcd $p |- (  A. x e. TIME ( x e. ( t_1 (,] t_2 ) /\ ph )  <-> 
  A. x e. TIME ( t_1 < x /\ x <_ t_2 /\ ph ) ) 
  $= ( cv cioc co wcel wa ctime wral cxr ax-mp bl.ert sseli bitri
  bitr4i wbr w3a clt wb simpl simpr pm3.2i elioc1 3anass anbi1i anass
  df-3an cle anbi2i ralbii bl.ralssi ) BFZCDGHIZAJZBKLUOMIZCUOUASZUOD
  UKSZATZJZBKLVABKLUQVBBKUQURUSUTJZAJZJZVBUQURVCJZAJVEUPVFAUPURUSUTTZ
  VFCMIZDMIZJUPVGUBVHVICKIZVHVJDKIZJZVJEVJVKUCNKMCOPNVKVIVLVKEVJVKUDN
  KMDOPNUECDUOUFNURUSUTUGQUHURVCAUIQVAVDURUSUTAUJULRUMVABKMOUNR $.
$}


${
  bl.allcc.1 $e |- ( t_1 e. TIME /\ t_2 e. TIME ) $.
$( Universal quantification over open time interval [t1 ,, t2]. $)
bl.allcc $p |- (  A. x e. TIME ( x e. ( t_1 (,) t_2 ) /\ ph )  <-> 
  A. x e. TIME ( t_1 < x /\ x < t_2 /\ ph ) ) 
  $= ( cv cioo wcel ctime wral cxr clt wbr w3a ax-mp bl.ert sseli
  bitr4i wa bitri co wb simpl simpr pm3.2i elioo1 3anass anbi1i anass
  df-3an anbi2i ralbii bl.ralssi ) BFZCDGUAHZASZBIJUNKHZCUNLMZUNDLMZA
  NZSZBIJUTBIJUPVABIUPUQURUSSZASZSZVAUPUQVBSZASVDUOVEAUOUQURUSNZVECKH
  ZDKHZSUOVFUBVGVHCIHZVGVIDIHZSZVIEVIVJUCOIKCPQOVJVHVKVJEVIVJUDOIKDPQ
  OUECDUNUFOUQURUSUGTUHUQVBAUITUTVCUQURUSAUJUKRULUTBIKPUMR $.
$}


${
  bl.alldc.1 $e |- ( t_1 e. TIME /\ t_2 e. TIME ) $.
$( Universal quantification over open-right time interval [t1 ., t2]. $)
bl.alldc $p |- (  A. x e. TIME ( x e. ( t_1 [,) t_2 ) /\ ph )  <-> 
  A. x e. TIME ( t_1 <_ x /\ x < t_2 /\ ph ) ) 
  $= ( cv cico co wcel wa ctime wral cxr ax-mp bl.ert sseli bitri
  bitr4i wbr w3a cle wb simpl simpr pm3.2i elico1 3anass anbi1i anass
  df-3an clt anbi2i ralbii bl.ralssi ) BFZCDGHIZAJZBKLUOMIZCUOUASZUOD
  UKSZATZJZBKLVABKLUQVBBKUQURUSUTJZAJZJZVBUQURVCJZAJVEUPVFAUPURUSUTTZ
  VFCMIZDMIZJUPVGUBVHVICKIZVHVJDKIZJZVJEVJVKUCNKMCOPNVKVIVLVKEVJVKUDN
  KMDOPNUECDUOUFNURUSUTUGQUHURVCAUIQVAVDURUSUTAUJULRUMVABKMOUNR $.
$}

$( Existential quantification over closed interval [t1 .. t2]. $)
bl.exdd $p |- ( E. x ( x e. ( t_1 [,] t_2 ) /\ ph ) <-> 
     -. A. x -. ( x e. ( t_1 [,] t_2 ) /\ ph ) )
   $= ( cv cicc co wcel wa df-ex ) BECDFGHAIBJ $.  

$( Existential quantification over open interval [t1 ,, t2]. $)
bl.excc $p |- ( E. x ( x e. ( t_1 (,) t_2 ) /\ ph ) <-> 
     -. A. x -. ( x e. ( t_1 (,) t_2 ) /\ ph ) )
   $= ( cv cioo co wcel wa df-ex ) BECDFGHAIBJ $.  

$( Existential quantification over open-left interval [t1 ,. t2]. $)
bl.excd $p |- ( E. x ( x e. ( t_1 (,] t_2 ) /\ ph ) <-> 
     -. A. x -. ( x e. ( t_1 (,] t_2 ) /\ ph ) )
   $= ( cv cioc co wcel wa df-ex ) BECDFGHAIBJ $. 

$( Existential quantification over open-right interval [t1 ., t2]. $)
bl.exdc $p |- ( E. x ( x e. ( t_1 [,) t_2 ) /\ ph ) <-> 
     -. A. x -. ( x e. ( t_1 [,) t_2 ) /\ ph ) )
   $= ( cv cico co wcel wa df-ex ) BECDFGHAIBJ $.  


$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                             BLESS LOGIC MODELS
                      
   ` mathfrakM ` provides values for variables at specific times: ` boldI [[ A , t_0 ]] `.
   Everything else, predicates, relations, and expressions are fixed for the 
   duration of computation.  Their values, at a particular time, are determined
   solely by the values of variables at that time.
   
   Some of the values of variables represent inputs to the program, say the 
   value of a temperature sensor; others represent outputs of the program, such 
   as the position of a valve.
   
   The values of all other variables are determined by the program.  Execution
   of a program constructs its model: ` mathfrakM `.
   
   Variables whose values don't change during computation (a.k.a. constants) are
   expressed as ` boldI [[ A ]] `.  Tautologies are expressed as ` boldI [[ ph ]] `.
   
   By their very nature, definitions of ` mathfrakM ` cannot be expressed as
   eliminatable definitions in Metamath.  Acceptabe Metamath definitions require 
   the defined symbol to occur only on the left side of a biconditional, with 
   thei right side using only previously defined symbols.  In this way, any wff
   which uses the new symbol can be reduced to only those defined in the axioms
   of logic and set theory.
   
   Therefore, the definitions of BL models are expressed as axioms:  ax-
   Hopefully some day, some clever mathematician will find a was to prove the
   axioms to remove the hyphen.
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$( Interpretation of predicates at all times. $)
wboldi  $a wff boldI [[ ph ]] $.

$( Interpretation of predicates at time ` t_0 `. $)
wboldit $a wff boldI [[ ph , t_0 ]] $.

$( Interpretation of values at all times. $)
wboldic $a class boldI [[ A ]] $.

$( Interpretation of values at time ` t_0 `. $)
wboldict $a class boldI [[ A , t_0 ]] $.

  
$( Tautologies hold in interpretation ` boldI `. 
   ax-bl.taut says that if ` ph ` is tautology, it also holds in interpretation ` boldI `. $)
ax-bl.taut $a |- ( ph -> boldI [[ ph ]] ) $.
  
$( Set membership  in interpretation ` boldI `. 
Types of variables are constant under interpretation ` boldI `. $)
bl.ty $p |- ( A e. B -> boldI [[ A e. B ]] )
  $= ? $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Logic Operators in interpretation ` boldI `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Interpretation of implication.  Only the sound (modal K-axiom) direction is
     axiomatized: the converse is false in general (Lean/Mathlib formalization,
     Lean4SFS/SFS.lean's dl_im_sound, found a counterexample). $)
df-bl.im $a |- ( boldI [[ ( ph -> ps ) ]]
      -> ( boldI [[ ph ]] -> boldI [[ ps ]] ) ) $.

  $( Monotonicity of ` boldI `: any provable implication lifts through the
     interpretation.  This is the general tool for weakening a plain-logic fact
     ` ( ph -> ps ) ` into a ` boldI `-level implication, used repeatedly below
     wherever a formerly-axiomatized converse direction (df-bl.or, df-bl.not,
     bl.3or, bl.ex, ...) was removed as unsound. $)
bl.mono $p |- ( ( ph -> ps ) -> ( boldI [[ ph ]] -> boldI [[ ps ]] ) )
  $= wph wps wi wph wps wi wboldi wph wboldi wps wboldi wi wph wps wi
  ax-bl.taut wph wps df-bl.im syl $.

  $( Interpretation of biconditional.  Only the sound direction is axiomatized:
     the converse is false in general (Lean4SFS/SFS.lean's dl_bi_sound). $)
df-bl.bi $a |- ( boldI [[ ( ph <-> ps ) ]]
      -> ( boldI [[ ph ]] <-> boldI [[ ps ]] ) ) $.

  $( Interpretation of conjunction.  $)
df-bl.an $a |- ( boldI [[ ( ph /\ ps ) ]] 
      <-> ( boldI [[ ph ]] /\ boldI [[ ps ]] ) ) $.
  
  $( Interpretation of conjunction, three wff.  $)
bl.3an $p |- ( boldI [[ ( ph /\ ps /\ ch ) ]] 
      <-> ( boldI [[ ph ]] /\ boldI [[ ps ]] /\ boldI [[ ch ]] ) ) 
  $= ( w3a wboldi wa wb ax-bl.taut ax-mp df-bl.bi ax-mp df-bl.an
  bitri df-3an anbi1i bitr4i ) ABCDZEZAEZBEZFZCEZFZSTUBDRABFZEZUBFZUC
  RUDCFZEZUFQUGGZEZRUHGUIUJABCNUIHIQUGJKUDCLMUEUAUBABLOMSTUBNP $.
  
  $( Interpretation of disjunction.  Only the sound direction is axiomatized: the
     converse (boldI[[ph\/ps]] -> boldI[[ph]]\/boldI[[ps]]) is false in general
     (Lean4SFS/SFS.lean's dl_or_sound). $)
df-bl.or $a |- ( ( boldI [[ ph ]] \/ boldI [[ ps ]] )
      -> boldI [[ ( ph \/ ps ) ]] ) $.
  
  $( Interpretation of disjunction, three wff.  Only the sound direction is
     axiomatized: the converse is false in general, same as df-bl.or itself
     (Lean4SFS/SFS.lean's dl_3or_sound). $)
bl.3or $p |- ( ( boldI [[ ph ]] \/ boldI [[ ps ]] \/ boldI [[ ch ]] )
      -> boldI [[ ( ph \/ ps \/ ch ) ]] )
  $= wph wboldi wps wboldi wch wboldi w3o wph wps wo wch wo wboldi wph wps
  wch w3o wboldi wph wboldi wps wboldi wch wboldi w3o wph wps wo wboldi wch
  wboldi wo wph wps wo wch wo wboldi wph wboldi wps wboldi wch wboldi w3o
  wph wboldi wps wboldi wo wch wboldi wo wph wps wo wboldi wch wboldi wo
  wph wboldi wps wboldi wch wboldi w3o wph wboldi wps wboldi wo wch wboldi
  wo wph wboldi wps wboldi wch wboldi df-3or biimpi wph wboldi wps wboldi
  wo wph wps wo wboldi wch wboldi wph wps df-bl.or orim1i syl wph wps wo
  wch df-bl.or syl wph wps wo wch wo wph wps wch w3o wi wph wps wo wch wo
  wboldi wph wps wch w3o wboldi wi wph wps wch w3o wph wps wo wch wo wph
  wps wch df-3or biimpri wph wps wo wch wo wph wps wch w3o bl.mono ax-mp
  syl $.
    
  $( Interpretation of complement.  Only the sound direction is axiomatized: the
     converse (-. boldI[[ph]] -> boldI[[-.ph]]) is false in general (Lean4SFS/
     SFS.lean's dl_not_sound). $)
df-bl.not $a |- ( boldI [[ -. ph  ]] -> -. boldI [[ ph ]] ) $.
  
$(  ***** Quantification in interpretation ` boldI ` ***** $)

  $( Exportation of universal quantification from interpretation ` boldI `. $)
df-bl.al $a |- ( boldI [[ A. x e. A ph ]] <-> A. x e. A boldI [[ ph ]] ) $.


  $( boldI respects logical equivalence -- the iff-congruence counterpart of
     bl.mono, same derivation pattern (ax-bl.taut necessitation + df-bl.bi's
     sound direction). $)
bl.monobi $p |- ( ( ph <-> ps ) -> ( boldI [[ ph ]] <-> boldI [[ ps ]] ) )
  $= wph wps wb wph wps wb wboldi wph wboldi wps wboldi wb wph wps wb
  ax-bl.taut wph wps df-bl.bi syl $.

  $( Unrestricted version of df-bl.al, via ralv (A. x e. _V ph <-> A. x ph). $)
bl.al $p |- ( boldI [[ A. x ph ]] <-> A. x boldI [[ ph ]] )
  $= wph vx wal wboldi wph vx cvv wral wboldi wph wboldi vx wal wph vx wal
  wph vx cvv wral wb wph vx wal wboldi wph vx cvv wral wboldi wb wph vx cvv
  wral wph vx wal wph vx ralv bicomi wph vx wal wph vx cvv wral bl.monobi
  ax-mp wph vx cvv wral wboldi wph wboldi vx cvv wral wph wboldi vx wal wph
  vx cvv df-bl.al wph wboldi vx ralv bitri bitri $.

  ${
  $( boldI[[ph]] is vacuously quantifiable whenever ph is: needed so bl.ex's
     witness-elimination step (rexlimi) has the F/ hypothesis it needs on the
     boldI-wrapped side, not just the raw side (nfre1). $)
  bl.nf.1 $e |- F/ x ph $.
  bl.nf $p |- F/ x boldI [[ ph ]]
    $= wph wboldi wph wboldi vx wal wi vx wal wph wboldi vx wnf wph wboldi
    wph wboldi vx wal wi vx wph wboldi vx wal wph wboldi wph wboldi vx wal
    wph vx wal wboldi wph wboldi wph vx bl.al wph vx wal wph wb wph vx wal
    wboldi wph wboldi wb wph vx bl.nf.1 19.3 wph vx wal wph bl.monobi ax-mp
    bitr3i biimpri ax-gen wph wboldi vx nf5-1 ax-mp $.
  $}

$( Define existential quantification in interpretation ` boldI `. $)
bl.dfrex2 $p |- ( boldI [[ E. x e. A ph ]] <-> boldI [[ -. A. x e. A -. ph ]] )
  $= ( wrex wn wral wb wboldi dfrex2 ax-bl.taut ax-mp df-bl.bi ax-mp
  ) ABCDZAEBCFEZGZHZNHOHGPQABCIPJKNOLM $.

  $( Raw (non-modal) restricted-existential-introduction fact, unconditional:
     the ordinary logic behind bl.ex, before any boldI is involved. $)
bl.exraw $p |- ( ( x e. A /\ ph ) -> E. x e. A ph )
  $= vx cv cA wcel wph wa vx cv cA wcel wph wa vx wex wph vx cA wrex vx cv
  cA wcel wph wa vx 19.8a wph vx cA wrex vx cv cA wcel wph wa vx wex wph vx
  cA df-rex biimpri syl $.

  $( Helper for bl.ex.  Built from bl.exraw, bl.mono, bl.ty (types are constant
     under interpretation -- one of this file's own pre-existing unproven $p
     placeholders, so this lemma inherits that gap rather than introducing a
     new one), and df-bl.an (sound both ways). $)
bl.exlem0 $p |- ( ( x e. A /\ boldI [[ ph ]] ) -> boldI [[ E. x e. A ph ]] )
  $= vx cv cA wcel wph wboldi wa vx cv cA wcel wph wa wboldi wph vx cA wrex
  wboldi vx cv cA wcel wph wboldi wa vx cv cA wcel wboldi wph wboldi wa vx
  cv cA wcel wph wa wboldi vx cv cA wcel vx cv cA wcel wboldi wph wboldi vx
  cv cA bl.ty anim1i vx cv cA wcel wph wa wboldi vx cv cA wcel wboldi wph
  wboldi wa vx cv cA wcel wph df-bl.an biimpri syl vx cv cA wcel wph wa wph
  vx cA wrex wi vx cv cA wcel wph wa wboldi wph vx cA wrex wboldi wi wph vx
  cA bl.exraw vx cv cA wcel wph wa wph vx cA wrex bl.mono ax-mp syl $.

  $( Exported form of bl.exlem0. $)
bl.exlem $p |- ( x e. A -> ( boldI [[ ph ]] -> boldI [[ E. x e. A ph ]] ) )
  $= vx cv cA wcel wph wboldi wph vx cA wrex wboldi wph vx cA bl.exlem0 ex $.

  $( Exportation of existential quantification from interpretation ` boldI `.
     Only the sound direction is axiomatized: the converse (the classic
     invalid dE.-to-E.d swap -- different instants may need different
     witnesses) is false in general (Lean4SFS/SFS.lean's dl_ex_sound). $)
bl.ex $p |- ( E. x e. A boldI [[ ph ]] -> boldI [[ E. x e. A ph ]] )
  $= wph wboldi wph vx cA wrex wboldi vx cA wph vx cA wrex vx wph vx cA
  nfre1 bl.nf wph vx cA bl.exlem rexlimi $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Arithmetic Operators in interpretation ` boldI `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


  ${
$(  df-bl.add.1 $e |- ( A e. RR /\ B e. RR ) $. $)
  $( Interpretation of addition.  $)
df-bl.add $a |- boldI [[ ( A + B ) ]] = 
      ( boldI [[ A ]] + boldI [[ B ]] ) $.
  $}

  ${
$(  df-bl.sub.1 $e |- ( A e. RR /\ B e. RR )  $. $)
  $( Interpretation of subtraction.  $)
df-bl.sub $a |- boldI [[ ( A - B ) ]] = 
      ( boldI [[ A ]] - boldI [[ B ]] ) $.
  $}

  ${
$(  df-bl.mul.1 $e |- ( A e. RR /\ B e. RR ) $. $)
  $( Interpretation of multiplication.  $)
df-bl.mul $a |- boldI [[ ( A x. B ) ]] 
      = ( boldI [[ A ]] x. boldI [[ B ]] ) $.
  $}

  ${
$(  df-bl.div.1 $e |- ( A e. RR /\ B e. RR ) $. $)
  $( Interpretation of division.  $)
df-bl.div $a |- boldI [[ ( A / B ) ]] = 
      ( boldI [[ A ]] / boldI [[ B ]] ) $.
  $}

  ${
$(  df-bl.um.1 $e |- A e. RR $. $)
  $( Interpretation of negation.  $)
df-bl.um $a |- boldI [[ -u A  ]]  = -u boldI [[ A ]] $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Relations in interpretation ` boldI `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Interpretation of equality.  $)
df-bl.eq $a |- ( boldI [[ A = B ]] <-> 
      boldI [[ A ]] = boldI [[ B ]] ) $.

  $( Interpretation of less-than.  $)
df-bl.lt $a |- ( boldI [[ A < B ]] <-> 
      boldI [[ A ]] < boldI [[ B ]] ) $.

  $( Interpretation of at-most.  $)
df-bl.am $a |- ( boldI [[ A <_ B ]] <-> 
      boldI [[ A ]] <_ boldI [[ B ]] ) $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Axioms for interpretation ` boldI ` at ` t_0 `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


  ${
  ax-bl.models.1 $e |- t_0 e. TIME $. 
$( Define interpretation of predicate for any ` t_0 e. TIME ` $)
ax-bl.models $a |- ( boldI [[ ph ]] -> boldI [[ ph , t_0 ]] ) $.
  $}

  ${
  ax-bl.modelsc.1 $e |- t_0 e. TIME $. 
$( Define interpretation of values over any ` t_0 e. TIME ` $)
ax-bl.modelsc $a |- ( boldI [[ A ]] = B -> 
      boldI [[ A , t_0 ]] = B )  $.
  $}

$( Axiom of temporal equivalence. $)
ax-bl.bi $a |- ( ( t_1 e. TIME /\ t_2 e. TIME /\ t_1 = t_2 ) ->
    ( ( ph <-> ps ) <-> 
       ( boldI [[ ph , t_1 ]] <-> boldI [[ ps , t_2 ]] ) ) )  $.
  
$( Axiom of temporal equality. $)
ax-bl.eq $a |- ( ( t_1 e. TIME /\ t_2 e. TIME /\ t_1 = t_2 ) ->
    ( A = B <-> boldI [[ A , t_1 ]] = boldI [[ B , t_2 ]] ) )  $.

  ${
  bl.monobit.1 $e |- t_0 e. TIME $.
  $( Same-instant specialization of ax-bl.bi: boldI[[.,t_0]] respects logical
     equivalence, at a single fixed t_0 (no second instant to unify away).
     Reused wherever a bl.ator3*-style proof needs to bridge a w3o-shaped
     3-way disjunction and its df-3or-equivalent nested 2-way form under the
     timed bracket. $)
  bl.monobit $p |- ( ( ph <-> ps ) -> ( boldI [[ ph , t_0 ]] <-> boldI [[ ps , t_0 ]] ) )
    $= wph wps wb wph vt0 wboldit wps vt0 wboldit wb vt0 ctime wcel vt0 ctime
    wcel vt0 vt0 wceq w3a wph wps wb wph vt0 wboldit wps vt0 wboldit wb wb
    vt0 ctime wcel vt0 ctime wcel vt0 vt0 wceq bl.monobit.1 bl.monobit.1 vt0
    eqid 3pm3.2i wph wps vt0 vt0 ax-bl.bi ax-mp biimpi $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Logic Operators in interpretation ` boldI ` at ` t_0 `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
  df-bl.bit.1 $e |- t_0 e. TIME $. 
  $( Interpretation of biconditional at time ` t_0 `.  $)
df-bl.bit $a |- ( boldI [[ ( ph <-> ps ) , t_0 ]] 
      <-> ( boldI [[ ph , t_0 ]] <-> boldI [[ ps , t_0 ]] ) ) $.
  $}

  ${
  df-bl.ant.1 $e |- t_0 e. TIME $. 
  $( Interpretation of conjunction at time ` t_0 `.  $)
df-bl.ant $a |- ( boldI [[ ( ph /\ ps ) , t_0 ]] 
      <-> ( boldI [[ ph , t_0 ]] /\ boldI [[ ps , t_0 ]] ) ) $.
  $}
  
  ${
  df-bl.an3t.1 $e |- t_0 e. TIME $.
  $( Interpretation of triple conjunction at time ` t_0 `.  $)
bl.an3t $p |- ( boldI [[ ( ph /\ ps /\ ch ) , t_0 ]] 
      <-> ( boldI [[ ph , t_0 ]] /\ boldI [[ ps , t_0 ]] 
      /\ boldI [[ ch , t_0 ]] ) )
  $= ( wa wboldit w3a df-bl.ant anbi1i wb df-3an ctime wcel wceq
  eqid 3pm3.2i ax-bl.bi ax-mp mpbi bitri 3bitr4i ) ABFZDGZCDGZFZADGZB
  DGZFZUEFABCHZDGZUGUHUEHUDUIUEABDEIJUKUCCFZDGZUFUJULKZUKUMKZABCLDMNZ
  UPDDOZHUNUOKUPUPUQEEDPQUJULDDRSTUCCDEIUAUGUHUELUB $.
  $} 
  
  ${
  df-bl.ort.1 $e |- t_0 e. TIME $. 
  $( Interpretation of disjunction at time ` t_0 `.  $)
df-bl.ort $a |- ( boldI [[ ( ph \/ ps ) , t_0 ]] 
      <-> ( boldI [[ ph , t_0 ]] \/ boldI [[ ps , t_0 ]] ) ) $.
  $}
  
  ${
  df-bl.or3t.1 $e |- t_0 e. TIME $.
  $( Interpretation of triple disjunction at time ` t_0 `.  $)
bl.or3t $p |- ( boldI [[ ( ph \/ ps \/ ch ) , t_0 ]] 
      <-> ( boldI [[ ph , t_0 ]] \/ boldI [[ ps , t_0 ]] 
      \/ boldI [[ ch , t_0 ]] ) )
  $= ( wo wboldit w3o df-bl.ort orbi1i wb df-3or ctime wcel wceq
  eqid w3a 3pm3.2i ax-bl.bi ax-mp mpbi bitri 3bitr4i ) ABFZDGZCDGZFZA
  DGZBDGZFZUFFABCHZDGZUHUIUFHUEUJUFABDEIJULUDCFZDGZUGUKUMKZULUNKZABCL
  DMNZUQDDOZQUOUPKUQUQUREEDPRUKUMDDSTUAUDCDEIUBUHUIUFLUC $.
  $} 
  
  ${
  df-bl.imt.1 $e |- t_0 e. TIME $. 
  $( Interpretation of implication at time ` t_0 `.  $)
df-bl.imt $a |- ( boldI [[ ( ph -> ps ) , t_0 ]] 
      <-> ( boldI [[ ph , t_0 ]] -> boldI [[ ps , t_0 ]] ) ) $.
  $}
  
  ${
  df-bl.nott.1 $e |- t_0 e. TIME $. 
  $( Interpretation of complement at time ` t_0 `.  $)
df-bl.nott $a |- ( boldI [[ -. ph  , t_0 ]] <-> -. boldI [[ ph , t_0 ]] ) $.
  $}


  ${
  bl.bitrit.1 $e |- t_0 e. TIME $.
  bl.bitrit.2 $e |- boldI [[ ( ph <-> ps ) , t_0 ]] $.
  bl.bitrit.3 $e |- boldI [[ ( ps <-> ch ) , t_0 ]] $.   
  $( Interpretation of transitive biconditional (~bitri) at time ` t_0 `.  $)
bl.bitrit $p |-  boldI [[ ( ph <-> ch ) , t_0 ]] 
  $= ( wb wboldit df-bl.bit mpbi bitri mpbir ) ACHDIADIZCDIZHNBDIZOA
  BHDINPHFABDEJKBCHDIPOHGBCDEJKLACDEJM $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Arithmetic Operators in interpretation ` boldI ` at ` t_0 `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


  ${
  df-bl.addt.1 $e |- t_0 e. TIME $. 
  $( Interpretation of addition at time ` t_0 `.  $)
df-bl.addt $a |- boldI [[ ( A + B ) , t_0 ]] = 
      ( boldI [[ A , t_0 ]] + boldI [[ B , t_0 ]] ) $.
  $}

  ${
  df-bl.subt.1 $e |- t_0 e. TIME  $. 
  $( Interpretation of subtraction at time ` t_0 `.  $)
df-bl.subt $a |- boldI [[ ( A - B ) , t_0 ]] = 
      ( boldI [[ A , t_0 ]] - boldI [[ B , t_0 ]] ) $.
  $}

  ${
  df-bl.mult.1 $e |- t_0 e. TIME $. 
  $( Interpretation of multiplication at time ` t_0 `.  $)
df-bl.mult $a |- boldI [[ ( A x. B ) , t_0 ]] 
      = ( boldI [[ A , t_0 ]] x. boldI [[ B , t_0 ]] ) $.
  $}

  ${
  df-bl.divt.1 $e |- t_0 e. TIME $. 
  $( Interpretation of division at time ` t_0 `.  $)
df-bl.divt $a |- boldI [[ ( A / B ) , t_0 ]] = 
      ( boldI [[ A , t_0 ]] / boldI [[ B , t_0 ]] ) $.
  $}

  ${
  df-bl.umt.1 $e |- t_0 e. TIME $. 
  $( Interpretation of negation at time ` t_0 `.  $)
df-bl.umt $a |- boldI [[ -u A  , t_0 ]]  = -u boldI [[ A , t_0 ]] $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Relations in interpretation ` boldI ` at ` t_0 `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
  df-bl.eqt.1 $e |- t_0 e. TIME $. 
  $( Interpretation of equality at time ` t_0 `.   $)
df-bl.eqt $a |- ( boldI [[ A = B , t_0 ]] <-> 
      boldI [[ A , t_0 ]] = boldI [[ B , t_0 ]] ) $.
  $}

  ${
  df-bl.ltt.1 $e |- t_0 e. TIME $. 
  $( Interpretation of less-than at time ` t_0 `.   $)
df-bl.ltt $a |- ( boldI [[ A < B , t_0 ]] <-> 
      boldI [[ A , t_0 ]] < boldI [[ B , t_0 ]] ) $.
  $}
  
  ${
  df-bl.amt.1 $e |- t_0 e. TIME $. 
  $( Interpretation of at-most at time ` t_0 `.   $)
df-bl.amt $a |- ( boldI [[ A <_ B , t_0 ]] <-> 
      boldI [[ A , t_0 ]] <_ boldI [[ B , t_0 ]] ) $.
  $}

  ${
  bl.tyt.1 $e |- t_0 e. TIME $. 
  $( Interpretation of retains type at time ` t_0 `.  
  Similar to ax-bl.ty, but applies to ` t_0 `. $)
bl.tyt $p |- ( A e. B  <->  boldI [[ A e. B , t_0 ]] ) 
  $= ? $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Quantification in interpretation ` boldI ` at ` t_0 `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


  ${
  $d x t_0 $.
  $d A t_0 $.
  bl.ralt.1 $e |- t_0 e. TIME $. 
$( Define restricted universal quantification in interpretation at time ` t_0 `. $)
df-bl.ralt $a |- ( boldI [[ A. x e. A ph , t_0 ]] 
      <->  A. x ( x e. A -> boldI [[ ph , t_0 ]] ) ) $.
  $}

  ${
  $d x t_0 $.
  $d A t_0 $.
  bl.rext.1 $e |- t_0 e. TIME $. 
$( Define restricted existential quantification in interpretation at time ` t_0 `. $)
df-bl.rext $a |- ( boldI [[ E. x e. A ph , t_0 ]] 
      <->  E. x ( x e. A /\ boldI [[ ph , t_0 ]] ) ) $.
  $}


 
$( 
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Temporal operator @ specifies time of occurence 
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(  Define @  $)

$( Define ` ( ph @ t_0 ) ` as a wff. $)
wat  $a wff ( ph @ t_0 ) $.

$( Define ` ( A @ t_0 ) ` as a class. $)
clat0 $a class ( A @ t_0 ) $.

  ${
  df-bl.at.1 $e |-  t_0 e. TIME $.
$( Definition of @ for predicates. 
   @ determines in which world to evaluate. $)
df-bl.at $a |- ( boldI [[ ( ph @ t_0 ) ]] <-> boldI [[ ph , t_0 ]] ) $.
	$}

  ${
  df-bl.atc.1 $e |-  t_0 e. TIME $.
$( Definition of @ for values. 
   @ determines in which world to evaluate. $)
df-bl.atc $a |- boldI [[ ( A @ t_0 ) ]] = boldI [[ A , t_0 ]] $.
	$}

  ${
  df-bl.at2.1 $e |-  t_1 e. TIME $.
  df-bl.at2.2 $e |-  t_2 e. TIME $.
$( Definition of Double @ for predicates.
   Second application of @ is inconsequential, predicate. $)
df-bl.at2 $a |- ( boldI [[ ( ( ph @ t_1 ) @ t_2 ) ]] 
           <-> boldI [[ ph , t_1 ]] ) $.
	$}
	
  ${
  df-bl.at2c.1 $e |-  t_1 e. TIME $.
  df-bl.at2c.2 $e |-  t_2 e. TIME $.
$( Definition of Double @ for values.
   Second application of @ is inconsequential, value. $)
df-bl.at2c $a |- boldI [[ ( ( A @ t_1 ) @ t_2 ) ]] = boldI [[ A , t_1 ]] $.
	$}
	
  ${
  bl.atintro.1 $e |-  t_0 e. TIME $.
$( @ Introduction for predicates. 
   If a predicate is always true it's true at any time. $)
bl.atintro $p |- ( boldI [[ ph ]] -> boldI [[ ( ph @ t_0 ) ]] )
  $= ( wboldi wboldit wat ax-bl.models df-bl.at sylibr ) ADABEABF
  DABCGABCHI $.
  $}

  ${
  df-bl.atbi.1 $e |-  t_1 e. TIME $.
  df-bl.atbi.2 $e |-  t_2 e. TIME $.
$( Definition of @ Equivalence (biconditional) for predicates. $)
df-bl.atbi $a |- ( ( t_1 = t_2 /\ ( ph <-> ps ) ) ->
    ( boldI [[ ( ph @ t_1 ) ]] <-> boldI [[ ( ps @ t_2 ) ]] ) ) $.
  $}

  ${
  bl.atbii.1 $e |-  t_1 e. TIME $.
  bl.atbii.2 $e |-  t_2 e. TIME $.
  bl.atbii.3 $e |- ( ph <-> ps ) $.
  bl.atbii.4 $e |- t_1 = t_2 $.
$( @ Equivalence (biconditional) for predicates, inference. $)
bl.atbii $p |- ( boldI [[ ( ph @ t_1 ) ]] <-> boldI [[ ( ps @ t_2 ) ]] ) 
  $= ( wceq wb wat wboldi df-bl.atbi mp2an ) CDIABJACKLBDKLJHGABCDEF
  MN $.
  $}

  ${
  df-bl.ateqc.1 $e |-  t_1 e. TIME $.
  df-bl.ateqc.2 $e |-  t_2 e. TIME $.
$( Definition of @ Equality for values. $)
df-bl.ateqc $a |- ( ( t_1 = t_2 /\ A = B ) ->
  boldI [[ ( A @ t_1 ) ]] = boldI [[ ( B @ t_2 ) ]] ) $.
  $}

  ${
  bl.ateqci.1 $e |-  t_1 e. TIME $.
  bl.ateqci.2 $e |-  t_2 e. TIME $.
  bl.ateqci.3 $e |- A = B $.
  bl.ateqci.4 $e |- t_1 = t_2 $.
$( Equality of @ for values, inference. $)
bl.ateqci $p |- boldI [[ ( A @ t_1 ) ]] = boldI [[ ( B @ t_2 ) ]] 
  $= ( wceq clat0 wboldic df-bl.ateqc mp2an ) CDIABIACJKBDJKIHGABCDE
  FLM $.
  $}

  ${
  bl.atintroc.1 $e |-  t_0 e. TIME $.
$( @ Introduction: if a value is constant its value is the same at any time. $)
bl.atintroc $p |- ( boldI [[ A ]] = B -> boldI [[ ( A @ t_0 ) ]] = B )
  $= ?
$(  ( wboldic wceq clat0 wboldict df-bl.atc ax-bl.modelsc syl5eq
  ) AEBFACGEACHBACDIABCDJK  $)
  $.
  $}


  ${
  bl.atrt.1 $e |-  t_0 e. TIME $.
$( Applying @ retains type. $)
df-bl.atrt $a |- (  A e. B  ->  boldI [[ ( A @ t_0 ) ]] e. B  ) $.
  $}


$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Distribute Temporal Operator @
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Distribute @ over logic
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$( Distribute @ over conjunction, two terms. $)
df-bl.atan2 $a |- ( t_0 e. TIME ->
  ( boldI [[ ( ( ph /\ ps ) @ t_0 ) ]] <-> 
       boldI [[ ( ( ph @ t_0 ) /\ ( ps @ t_0 ) ) ]] ) ) $.

  ${
  bl.atan2i.1 $e |- t_0 e. TIME $.
$( Distribute @ over conjunction, two terms, inference. $)
bl.atan2i $p |- ( boldI [[ ( ( ph /\ ps ) @ t_0 ) ]] 
      <-> boldI [[ ( ( ph @ t_0 ) /\ ( ps @ t_0 ) ) ]] ) 
  $= ( ctime wcel wa wat wboldi wb df-bl.atan2 ax-mp ) CEFABGCHIACHB
  CHGIJDABCKL $.
  $} 

  ${
  bl.atan3i.1 $e |- t_0 e. TIME $.
$( Distribute @ over conjunction, three terms, inference. $)
bl.atan3i $p |- ( boldI [[ ( ( ph /\  ps /\ ch ) @ t_0 ) ]] 
      <-> boldI [[ ( ( ph @ t_0 ) /\ ( ps @ t_0 ) /\ ( ch @ t_0 ) ) ]] ) 
  $= ( w3a wat wboldi wboldit wa df-bl.at wb df-3an wcel wceq
  eqid ctime bitri df-bl.ant bitr4i 3pm3.2i ax-bl.bi mpbi anbi1i
  3anbi123i ax-mp bl.3an ) ABCFZDGHZADGZHZBDGZHZCDGZHZFZUJULUNFHUIADI
  ZBDIZCDIZFZUPUIUQURJZUSJZUTUIABJZDIZUSJZVBUIVCCJZDIZVEUIUHDIZVGUHDE
  KUHVFLZVHVGLZABCMDQNZVKDDOZFVIVJLVKVKVLEEDPUAUHVFDDUBUFUCRVCCDESRVD
  VAUSABDESUDRUQURUSMTUKUQUMURUOUSADEKBDEKCDEKUETUJULUNUGT $.
  $} 
  
  ${
  bl.atan3ri.1 $e |- t_0 e. TIME $.
$( Distribute @ over conjunction, three terms (right), inference. $)
bl.atan3ri $p |- ( boldI [[ ( ( ph /\ ( ps /\ ch ) ) @ t_0 ) ]] 
      <-> boldI [[ ( ( ph @ t_0 ) /\ ( ( ps @ t_0 ) /\ ( ch @ t_0 ) ) ) ]] ) 
  $= ( wat wa wboldi df-bl.an wboldit wceq wb eqid df-3an
  df-bl.at w3a bitri df-bl.ant anbi12i bitr4i anass pm3.2i ax-mp
  3bitri bicomi df-bl.atbi anbi2i 3bitr2ri ) ADFZBDFZCDFZGZGHUIHZULHZ
  GZABCPZDFHZABCGZGZDFHZUIULIUQUMUJHZUKHZGZGZUOUQADJZURDJZGZVDUQUTUSD
  JVGDDKZUPUSLZGUQUTLVHVIDMUPABGCGUSABCNABCUAQUBUPUSDDEEUFUCZUSDEOAUR
  DERUDVEUMVFVCUMVEADEOUEVFBDJZCDJZGVCBCDERVAVKVBVLBDEOCDEOSTSQUNVCUM
  UJUKIUGTVJUH $.
  $} 

  ${
  bl.atan3li.1 $e |- t_0 e. TIME $.
$( Distribute @ over conjunction, three terms (left), inference. $)
bl.atan3li $p |- ( boldI [[ ( ( ( ph /\ ps ) /\ ch ) @ t_0 ) ]] 
      <-> boldI [[ ( ( ( ph @ t_0 ) /\ ( ps @ t_0 ) ) /\ ( ch @ t_0 ) ) ]] ) 
  $= ( wat wa wboldi df-bl.an wboldit wceq wb eqid df-3an
  df-bl.at w3a pm3.2i df-bl.ant anbi12i bitr4i df-bl.atbi 3bitri
  bicomi anbi1i ax-mp bitri 3bitr2ri ) ADFZBDFZGZCDFZGHUJHZUKHZGZABCP
  ZDFHZABGZCGZDFHZUJUKIUPUHHZUIHZGZUMGZUNUPUQDJZCDJZGZVCUPUSURDJVFDDK
  ZUOURLZGUPUSLVGVHDMABCNQUOURDDEEUAUEZURDEOUQCDERUBVDVBVEUMVDADJZBDJ
  ZGVBABDERUTVJVAVKADEOBDEOSTUMVECDEOUCSUFULVBUMUHUIIUDTVIUG $.
  $} 

$( Distribute @ over disjunction, two terms. $)
df-bl.ator2 $a |- ( t_0 e. TIME ->
  ( boldI [[ ( ( ph \/ ps ) @ t_0 ) ]] 
        <-> boldI [[ ( ( ph @ t_0 ) \/ ( ps @ t_0 ) ) ]] ) ) $.

  ${
  bl.ator2i.1 $e |- t_0 e. TIME $.
$( Distribute @ over disjunction, two terms, inference. $)
bl.ator2i $p |- ( boldI [[ ( ( ph \/ ps ) @ t_0 ) ]]
      <-> boldI [[ ( ( ph @ t_0 ) \/ ( ps @ t_0 ) ) ]] )
  $= ( ctime wcel wo wat wboldi wb df-bl.ator2 ax-mp ) CEFABGCHIACHB
  CHGIJDABCKL $.
  $}

  ${
  bl.ator3i.1 $e |- t_0 e. TIME $.
$( Distribute @ over disjunction, three terms, inference.  Restated to keep
   the disjuncts separately boldI[[.]]-wrapped rather than re-wrapping the
   whole disjunction (as the original did, via the now-weakened bl.3or): that
   re-wrap needed bl.3or's full (now-unsound-in-general) biconditional, and
   this form is exactly what the proof already establishes from only the
   sound @/timed-bracket machinery (df-bl.at/df-bl.ort/df-3or), so nothing is
   lost -- see Lean4SFS/SFS.lean's dl_3or_sound finding. $)
bl.ator3i $p |- ( boldI [[ ( ( ph \/ ps \/ ch ) @ t_0 ) ]]
      <-> ( boldI [[ ( ph @ t_0 ) ]] \/ boldI [[ ( ps @ t_0 ) ]] \/ boldI [[ ( ch @ t_0 ) ]] ) )
  $= wph wps wch w3o vt0 wat wboldi wph vt0 wboldit wps vt0 wboldit wch vt0
  wboldit w3o wph vt0 wat wboldi wps vt0 wat wboldi wch vt0 wat wboldi w3o
  wph wps wch w3o vt0 wat wboldi wph vt0 wboldit wps vt0 wboldit wo wch vt0
  wboldit wo wph vt0 wboldit wps vt0 wboldit wch vt0 wboldit w3o wph wps wch
  w3o vt0 wat wboldi wph wps wch w3o vt0 wboldit wph vt0 wboldit wps vt0
  wboldit wo wch vt0 wboldit wo wph wps wch w3o vt0 bl.ator3i.1 df-bl.at wph
  wps wch w3o vt0 wboldit wph wps wo wch wo vt0 wboldit wph vt0 wboldit wps
  vt0 wboldit wo wch vt0 wboldit wo wph wps wch w3o wph wps wo wch wo wb
  wph wps wch w3o vt0 wboldit wph wps wo wch wo vt0 wboldit wb wph wps wch
  df-3or wph wps wch w3o wph wps wo wch wo vt0 bl.ator3i.1 bl.monobit ax-mp
  wph wps wo wch wo vt0 wboldit wph wps wo vt0 wboldit wch vt0 wboldit wo
  wph vt0 wboldit wps vt0 wboldit wo wch vt0 wboldit wo wph wps wo wch vt0
  bl.ator3i.1 df-bl.ort wph wps wo vt0 wboldit wph vt0 wboldit wps vt0
  wboldit wo wch vt0 wboldit wph wps vt0 bl.ator3i.1 df-bl.ort orbi1i bitri
  bitri bitri wph vt0 wboldit wps vt0 wboldit wch vt0 wboldit df-3or bitr4i
  wph vt0 wat wboldi wph vt0 wboldit wps vt0 wat wboldi wps vt0 wboldit wch
  vt0 wat wboldi wch vt0 wboldit wph vt0 bl.ator3i.1 df-bl.at wps vt0
  bl.ator3i.1 df-bl.at wch vt0 bl.ator3i.1 df-bl.at 3orbi123i bitr4i $.
  $}

  ${
  bl.ator3ri.1 $e |- t_0 e. TIME $.
$( Distribute @ over disjunction, three terms (right), inference.  Restated
   for the same reason as bl.ator3i above. $)
bl.ator3ri $p |- ( boldI [[ ( ( ph \/ ( ps \/ ch ) ) @ t_0 ) ]]
      <-> ( boldI [[ ( ph @ t_0 ) ]] \/ ( boldI [[ ( ps @ t_0 ) ]] \/ boldI [[ ( ch @ t_0 ) ]] ) ) )
  $= wph wps wch wo wo vt0 wat wboldi wph wps wch wo wo vt0 wboldit wph vt0
  wat wboldi wps vt0 wat wboldi wch vt0 wat wboldi wo wo wph wps wch wo wo
  vt0 bl.ator3ri.1 df-bl.at wph wps wch wo wo vt0 wboldit wph vt0 wboldit
  wps wch wo vt0 wboldit wo wph vt0 wat wboldi wps vt0 wat wboldi wch vt0
  wat wboldi wo wo wph wps wch wo vt0 bl.ator3ri.1 df-bl.ort wph vt0 wboldit
  wph vt0 wat wboldi wps wch wo vt0 wboldit wps vt0 wat wboldi wch vt0 wat
  wboldi wo wph vt0 wat wboldi wph vt0 wboldit wph vt0 bl.ator3ri.1 df-bl.at
  bicomi wps wch wo vt0 wboldit wps vt0 wboldit wch vt0 wboldit wo wps vt0
  wat wboldi wch vt0 wat wboldi wo wps wch vt0 bl.ator3ri.1 df-bl.ort wps
  vt0 wboldit wps vt0 wat wboldi wch vt0 wboldit wch vt0 wat wboldi wps vt0
  wat wboldi wps vt0 wboldit wps vt0 bl.ator3ri.1 df-bl.at bicomi wch vt0
  wboldit wch vt0 wat wboldi wch vt0 wat wboldi wch vt0 wat wboldi wch vt0
  wboldit wch vt0 bl.ator3ri.1 df-bl.at bicomi wch vt0 wat wboldi biid bitri
  orbi12i bitri orbi12i bitri bitri $.
  $}

  ${
  bl.ator3li.1 $e |- t_0 e. TIME $.
$( Distribute @ over disjunction, three terms (left), inference.  Restated
   for the same reason as bl.ator3i above. $)
bl.ator3li $p |- ( boldI [[ ( ( ( ph \/ ps ) \/ ch ) @ t_0 ) ]]
      <-> ( ( boldI [[ ( ph @ t_0 ) ]] \/ boldI [[ ( ps @ t_0 ) ]] ) \/ boldI [[ ( ch @ t_0 ) ]] ) )
  $= wph wps wo wch wo vt0 wat wboldi wph wps wo wch wo vt0 wboldit wph vt0 wat
  wboldi wps vt0 wat wboldi wo wch vt0 wat wboldi wo wph wps wo wch wo vt0
  bl.ator3li.1 df-bl.at wph wps wo wch wo vt0 wboldit wph wps wo vt0 wboldit
  wch vt0 wboldit wo wph vt0 wat wboldi wps vt0 wat wboldi wo wch vt0 wat
  wboldi wo wph wps wo wch vt0 bl.ator3li.1 df-bl.ort wph wps wo vt0 wboldit
  wph vt0 wat wboldi wps vt0 wat wboldi wo wch vt0 wboldit wch vt0 wat wboldi
  wph wps wo vt0 wboldit wph vt0 wboldit wps vt0 wboldit wo wph vt0 wat wboldi
  wps vt0 wat wboldi wo wph wps vt0 bl.ator3li.1 df-bl.ort wph vt0 wboldit wph
  vt0 wat wboldi wps vt0 wboldit wps vt0 wat wboldi wph vt0 wat wboldi wph vt0
  wboldit wph vt0 bl.ator3li.1 df-bl.at bicomi wps vt0 wat wboldi wps vt0
  wboldit wps vt0 bl.ator3li.1 df-bl.at bicomi orbi12i bitri wch vt0 wat
  wboldi wch vt0 wboldit wch vt0 bl.ator3li.1 df-bl.at bicomi orbi12i bitri
  bitri $.
  $}

$( Distribute @ over biconditional. $)
df-bl.atbid $a |- ( t_0 e. TIME ->
 ( boldI [[ ( ( ph <-> ps ) @ t_0 ) ]] 
       <-> boldI [[ ( ( ph @ t_0 ) <-> ( ps @ t_0 ) ) ]] ) ) $.

  ${
  bl.atbidi.1 $e |- t_0 e. TIME $.
$( Distribute @ over biconditional, inference. $)
bl.atbidi $p |- ( boldI [[ ( ( ph <-> ps ) @ t_0 ) ]] 
      <-> boldI [[ ( ( ph @ t_0 ) <-> ( ps @ t_0 ) ) ]] )
  $= ( ctime wcel wb wat wboldi df-bl.atbid ax-mp ) CEFABGCHIACHBCHGI
  GDABCJK $.
  $}

$( Distribute @ over complement $)
df-bl.atnot $a |- ( t_0 e. TIME ->
	 boldI [[ ( ( -. ph @ t_0 ) <-> -. ( ph @ t_0 ) ) ]] ) $.

  ${
  bl.atnot.1 $e |- t_0 e. TIME $.
$( Distribute @ over complement, inference $)
bl.atnoti $p |- boldI [[ ( ( -. ph @ t_0 ) <-> -. ( ph @ t_0 ) ) ]]
  $= ( ctime wcel wn wat wb wboldi df-bl.atnot ax-mp ) BDEAFBGABGFHI
  CABJK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Distribute @ over arithmetic
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$( Distribute @ over addition, two terms. $)
df-bl.atad2 $a |- ( ( t_0 e. TIME /\ B e. RR /\ C e. RR ) ->
 boldI [[ ( ( B + C ) @ t_0 ) ]] 
       = boldI [[ ( ( B @ t_0 ) + ( C @ t_0 ) ) ]] ) $.

  ${
  bl.atad2i.1 $e |- ( t_0 e. TIME /\ B e. RR /\ C e. RR ) $.
$( Distribute @ over addition, two terms, inference. $)
bl.atad2i $p |- boldI [[ ( ( B + C ) @ t_0 ) ]]
      = boldI [[ ( ( B @ t_0 ) + ( C @ t_0 ) ) ]]
  $= ( ctime wcel cr w3a caddc clat0 wboldic wceq df-bl.atad2 ax-mp
  co ) CEFAGFBGFHABIOCJKACJBCJIOKLDABCMN $.
  $}

$( Distribute @ over multiplication, two terms. $)
df-bl.atmul2 $a |- ( ( t_0 e. TIME /\ B e. RR /\ C e. RR ) ->
  boldI [[ ( ( B x. C ) @ t_0 ) ]] 
        = boldI [[ ( ( B @ t_0 ) x. ( C @ t_0 ) ) ]] ) $.

  ${
  bl.atmul2i.1 $e |- ( t_0 e. TIME /\ B e. RR /\ C e. RR ) $.
$( Distribute @ over multiplication, two terms, inference. $)
bl.atmul2i $p |- boldI [[ ( ( B x. C ) @ t_0 ) ]]
      = boldI [[ ( ( B @ t_0 ) x. ( C @ t_0 ) ) ]]
  $= ( ctime wcel cr w3a cmul clat0 wboldic wceq df-bl.atmul2 ax-mp
  co ) CEFAGFBGFHABIOCJKACJBCJIOKLDABCMN $.
  $}

$( Distribute @ over subtraction. $)
df-bl.atsub $a |- ( ( t_0 e. TIME /\ B e. RR /\ C e. RR ) ->
  boldI [[ ( ( B - C ) @ t_0 ) ]]
        = boldI [[ ( ( B @ t_0 ) - ( C @ t_0 ) ) ]] ) $.

  ${
  bl.atsubi.1 $e |- ( t_0 e. TIME /\ B e. RR /\ C e. RR ) $.
$( Distribute @ over subtraction, inference. $)
bl.atsubi $p |- boldI [[ ( ( B - C ) @ t_0 ) ]] 
      = boldI [[ ( ( B @ t_0 ) - ( C @ t_0 ) ) ]]
  $= ( ctime wcel cr w3a cmin co clat0 wboldic wceq df-bl.atsub
  ax-mp ) CEFAGFBGFHABIJCKLACKBCKIJLMDABCNO $.
  $}

$( Distribute @ over division. $)
df-bl.atdiv $a |- ( ( t_0 e. TIME /\ B e. RR /\ C e. RR ) ->
  boldI [[ ( ( B / C ) @ t_0 ) ]] 
        = boldI [[ ( ( B @ t_0 ) / ( C @ t_0 ) ) ]] ) $.

  ${
  bl.atdivi.1 $e |- ( t_0 e. TIME /\ B e. RR /\ C e. RR ) $.
$( Distribute @ over division, inference. $)
bl.atdivi $p |- boldI [[ ( ( B / C ) @ t_0 ) ]]
      = boldI [[ ( ( B @ t_0 ) / ( C @ t_0 ) ) ]]
  $= ( ctime wcel cr w3a cdiv co clat0 wboldic wceq df-bl.atdiv
  ax-mp ) CEFAGFBGFHABIJCKLACKBCKIJLMDABCNO $.
  $}  

$( Distribute @ over unary minus. $)
df-bl.atum $a |- ( t_0 e. TIME ->
  boldI [[ ( -u A @ t_0 ) ]] = boldI [[ -u ( A @ t_0 ) ]] ) $.

  ${
  bl.atumi.1 $e |- t_0 e. TIME $.
$( Distribute @ over unary minus, inference. $)
bl.atumi $p |- boldI [[ ( -u A @ t_0 ) ]] = boldI [[ -u ( A @ t_0 ) ]]
  $= ( ctime wcel cneg clat0 wboldic wceq df-bl.atum ax-mp ) BDEAFBG
  HABGFHICABJK $.
  $}

  ${
  bl.atad3.1 $e |- t_0 e. TIME $.
  bl.atad3.2 $e |- A e. RR $.
  bl.atad3.3 $e |- B e. RR $.
  bl.atad3.4 $e |- C e. RR $.
$( Distribute @ over addition, three terms ` ( A + ( B + C ) ) @ t_0 ) `. $)
bl.atad3 $p |- boldI [[ ( ( A + ( B + C ) ) @ t_0 ) ]] 
      = boldI [[ ( ( A @ t_0 ) + ( ( B @ t_0 ) + ( C @ t_0 ) ) ) ]]
  $= ( caddc co clat0 wboldic ctime wcel readdcli bl.atad2i
  df-bl.add cr 3pm3.2i oveq2i 3eqtri eqtr4i ) ABCIJZIJDKLZADKZLZBDKCD
  KIJZLZIJZUEUGIJLUDUEUCDKZIJLUFUJLZIJUIAUCDDMNZARNUCRNEFBCGHOSPUEUJQ
  UKUHUFIBCDULBRNCRNEGHSPTUAUEUGQUB $.
  $}
 
  ${
  bl.atad3l.1 $e |- t_0 e. TIME $.
  bl.atad3l.2 $e |- A e. RR $.
  bl.atad3l.3 $e |- B e. RR $.
  bl.atad3l.4 $e |- C e. RR $.
$( Distribute @ over addition, three terms, left ` ( ( A + B ) + C ) @ t_0 ) `. $)
bl.atad3l $p |- boldI [[ ( ( ( A + B ) + C ) @ t_0 ) ]]
      = boldI [[ ( ( ( A @ t_0 ) + ( B @ t_0 ) ) + ( C @ t_0 ) ) ]]
  $= ( caddc co clat0 wboldic ctime wcel readdcli bl.atad2i
  df-bl.add cr 3pm3.2i oveq1i 3eqtri eqtr4i ) ABIJZCIJDKLZADKBDKIJZLZ
  CDKZLZIJZUEUGIJLUDUCDKZUGIJLUJLZUHIJUIUCCDDMNZUCRNCRNEABFGOHSPUJUGQ
  UKUFUHIABDULARNBRNEFGSPTUAUEUGQUB $.
  $}

  ${
  bl.atad.1 $e |- ( t_0 e. TIME /\ +( cl_1 )x e. RR /\ +( cl_2 )x e. RR ) $.
$( Distribute @ over addition, class list. $)
bl.atad $p |- boldI [[ ( +( cl_1 , cl_2 )x @ t_0 ) ]] 
      = boldI [[ ( ( +( cl_1 )x @ t_0 ) + ( +( cl_2 )x @ t_0 ) ) ]]
  $= ( bl.cln bl.cadd clat0 wboldic caddc co ctime wcel cr
  df-bl.add2 simp1i eqid bl.ateqci w3a wceq df-bl.atad2 ax-mp eqtri )
  ABEFZCGHAFZBFZIJZCGHZUDCGUECGIJHZUCUFCCCKLZUDMLZUEMLZDOZULABNCPQUIU
  JUKRUGUHSDUDUECTUAUB $.
  $}
 
  ${
  bl.atmul3.1 $e |- t_0 e. TIME $.
  bl.atmul3.2 $e |- A e. RR $.
  bl.atmul3.3 $e |- B e. RR $.
  bl.atmul3.4 $e |- C e. RR $.
$( Distribute @ over multiplication, three terms ` ( A x. ( B x. C ) ) @ t_0 ) `. $)
bl.atmul3 $p |- boldI [[ ( ( A x. ( B x. C ) ) @ t_0 ) ]]
      = boldI [[ ( ( A @ t_0 ) x. ( ( B @ t_0 ) x. ( C @ t_0 ) ) ) ]]
  $= ( cmul co clat0 wboldic ctime wcel cr remulcli 3pm3.2i
  df-bl.mul bl.atmul2i oveq2i 3eqtri eqtr4i ) ABCIJZIJDKLZADKZLZBDKCD
  KIJZLZIJZUEUGIJLUDUEUCDKZIJLUFUJLZIJUIAUCDDMNZAONUCONEFBCGHPQSUEUJR
  UKUHUFIBCDULBONCONEGHQSTUAUEUGRUB $.
  $}
 
  ${
  bl.atmul3l.1 $e |- t_0 e. TIME $.
  bl.atmul3l.2 $e |- A e. RR $.
  bl.atmul3l.3 $e |- B e. RR $.
  bl.atmul3l.4 $e |- C e. RR $.
$( Distribute @ over multiplication, three terms, left ` ( ( A x. B ) x. C ) @ t_0 ) `. $)
bl.atmul3l $p |- boldI [[ ( ( ( A x. B ) x. C ) @ t_0 ) ]] 
      = boldI [[ ( ( ( A @ t_0 ) x. ( B @ t_0 ) ) x. ( C @ t_0 ) ) ]]  
  $= ( cmul co clat0 wboldic ctime wcel cr remulcli 3pm3.2i
  df-bl.mul bl.atmul2i oveq1i 3eqtri eqtr4i ) ABIJZCIJDKLZADKBDKIJZLZ
  CDKZLZIJZUEUGIJLUDUCDKZUGIJLUJLZUHIJUIUCCDDMNZUCONCONEABFGPHQSUJUGR
  UKUFUHIABDULAONBONEFGQSTUAUEUGRUB $.
  $}

  ${
  bl.atmul.1 $e |- ( t_0 e. TIME /\ *( cl_1 )x e. RR /\ *( cl_2 )x e. RR ) $.
$( Distribute @ over multiplication, class list. $)
bl.atmul $p |- boldI [[ ( *( cl_1 , cl_2 )x @ t_0 ) ]] 
      = boldI [[ ( ( *( cl_1 )x @ t_0 ) x. ( *( cl_2 )x @ t_0 ) ) ]]
  $= ( bl.cln bl.cmul clat0 wboldic cmul ctime wcel simp1i
  df-bl.mul2 co cr eqid bl.ateqci w3a wceq df-bl.atmul2 ax-mp eqtri )
  ABEFZCGHAFZBFZINZCGHZUDCGUECGINHZUCUFCCCJKZUDOKZUEOKZDLZULABMCPQUIU
  JUKRUGUHSDUDUECTUAUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Distribute @ over relations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$( Distribute @ over equality. $)
df-bl.ateq $a |- ( ( t_0 e. TIME /\ A e. RR /\ B e. RR ) -> 
  ( boldI [[ ( A = B @ t_0 ) ]] 
      <-> boldI [[ ( A @ t_0 ) = ( B @ t_0 ) ]] ) ) $.

  ${
  bl.ateq.1 $e |-  t_0 e. TIME  $.
  bl.ateq.2 $e |- ( A e. RR /\ B e. RR ) $.
$( Distribute @ over equality, inference. $)
bl.ateq $p |- ( boldI [[ ( A = B @ t_0 ) ]]
    <-> boldI [[ ( A @ t_0 ) = ( B @ t_0 ) ]] )
  $= ( ctime wcel cr w3a wceq wat wboldi clat0 wb pm3.2i anass
  df-3an wa mpbir df-bl.ateq ax-mp ) CFGZAHGZBHGZIZABJCKLACMBCMJLNUEU
  BUCRUDRZUFUBUCUDRZRUBUGDEOUBUCUDPSUBUCUDQSABCTUA $.
  $}

$( Distribute @ over less than. $)
df-bl.atlt $a |- ( ( t_0 e. TIME /\ A e. RR /\ B e. RR ) -> 
  ( boldI [[ ( A < B @ t_0 ) ]] 
      <-> boldI [[ ( A @ t_0 ) < ( B @ t_0 ) ]] ) ) $.

  ${
  bl.atlti.1 $e |-  t_0 e. TIME  $.
  bl.atlti.2 $e |- ( A e. RR /\ B e. RR ) $.
$( Distribute @ over less than, inference. $)
bl.atlti $p |- ( boldI [[ ( A < B @ t_0 ) ]] 
    <-> boldI [[ ( A @ t_0 ) < ( B @ t_0 ) ]] )
  $= ( ctime cr w3a clt wbr wat wboldi clat0 wb wa pm3.2i anass
  mpbir wcel df-3an df-bl.atlt ax-mp ) CFSZAGSZBGSZHZABIJCKLACMBCMIJL
  NUFUCUDOUEOZUGUCUDUEOZOUCUHDEPUCUDUEQRUCUDUETRABCUAUB $.
  $}

  ${
  bl.atami.1 $e |-  t_0 e. TIME  $.
  bl.atami.2 $e |- ( A e. RR /\ B e. RR ) $.
$( Distribute @ over at most, inference. $)
bl.atami $p |- ( boldI [[ ( A <_ B @ t_0 ) ]] 
    <-> boldI [[ ( A @ t_0 ) <_ ( B @ t_0 ) ]] ) 
  $= ( cle wbr wat wboldi wboldic wboldit wboldict
  df-bl.amt clat0 df-bl.at df-bl.atc breq12i 3bitr4i df-bl.am bitr4i
  ) ABFGZCHIZACNZJZBCNZJZFGZUCUEFGIUACKACLZBCLZFGUBUGABCDMUACDOUDUHUF
  UIFACDPBCDPQRUCUEST $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Distribute @ over quantification
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$( Distribute @ over universal quantification. $)
df-bl.atal $a |- ( t_0 e. TIME -> 
  ( boldI [[ ( A. x e. A ph @ t_0 ) ]] 
    <-> boldI [[ A. x e. A ( ph @ t_0 ) ]] ) ) $.

  ${
  df-bl.atexi.1 $e |- t_0 e. TIME $.
$( Distribute @ over existential quantification, inference. $)
df-bl.atexi $a |- ( boldI [[ ( E. x e. A ph @ t_0 ) ]] 
      <-> boldI [[ E. x e. A ( ph @ t_0 ) ]] ) $.
  $}
  

$( Distribute @ over summation. $)
df-bl.atsum $a |- ( t_0 e. TIME -> 
  boldI [[ ( sum_ x e. A B @ t_0 ) ]] = boldI [[ sum_ x e. A ( B @ t_0 ) ]] ) $.

$( Distribute @ over product. $)
df-bl.atprod $a |- ( t_0 e. TIME -> 
  boldI [[ ( prod_ x e. A B @ t_0 ) ]] = boldI [[ prod_ x e. A ( B @ t_0 ) ]] ) $.

  
  ${
  df-bl.atqq.1 $e |-  t_0 e. TIME $.
$( Distribute @ over conditional expression. $)
df-bl.atqq $a |- boldI [[ ( if ( ph , A , B ) @ t_0 ) ]]
      = boldI [[ if ( ( ph @ t_0 ) , ( A @ t_0 ) , ( B @ t_0 ) ) ]] $.
  $}


 
$( 
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Temporal operator ` ^. ` shifts reference to time of occurence 
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  
$( Define ` ( ph ^. A ) ` as a wff $)
wts $a wff ( ph ^. A ) $.

$( Define ` ( A ^. B ) ` as a class $)
clats $a class ( A ^. B ) $.

$( Definition of time-shift predicate. $)
df-bl.ts $a |- ( ( A e. ZZ /\ ( D e. RR /\ t_0 e. TIME /\ ( t_0 + ( D x. A ) ) e. TIME ) ) -> 
		( boldI [[ ( ph ^. A ) , t_0 ]] <-> 
		boldI [[ ph , ( t_0 + ( D x. A ) ) ]] ) ) $.

	
$( Definition of time-shift value. $)
df-bl.tsc $a |- ( ( B e. ZZ /\ ( D e. RR /\ t_0 e. TIME /\ ( t_0 + ( D x. B ) ) e. TIME ) ) -> 
		boldI [[ ( A ^. B ) , t_0 ]] = boldI [[ A , ( t_0 + ( D x. B ) ) ]] ) $.

${
  bl.tsi.1 $e |- A e. ZZ $.
  bl.tsi.2 $e |- D e. RR $.
  bl.tsi.3 $e |- t_0 e. TIME $.
  bl.tsi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Time-shift predicate, inference. $)
bl.tsi $p |- ( boldI [[ ( ph ^. A ) , t_0 ]] <-> 
		boldI [[ ph , ( t_0 + ( D x. A ) ) ]] )
  $= ( cz wcel cr ctime cmul co caddc w3a wts wboldit wb 3pm3.2i
  df-bl.ts mp2an ) BIJCKJZDLJZDCBMNONZLJZPABQDRAUERSEUCUDUFFGHTABCDUA
  UB $.
$}		
 
			
${
  bl.tsci.1 $e |- B e. ZZ $.
  bl.tsci.2 $e |- D e. RR $.
  bl.tsci.3 $e |- t_0 e. TIME $.
  bl.tsci.4 $e |- ( t_0 + ( D x. B ) ) e. TIME $.	  
$( Time-shift value, inference  $)
bl.tsci $p |- boldI [[ ( A ^. B ) , t_0 ]] 
      = boldI [[ A , ( t_0 + ( D x. B ) ) ]]
  $= ( cz wcel cr ctime cmul co caddc w3a clats wboldict wceq 3pm3.2i
  df-bl.tsc mp2an ) BIJCKJZDLJZDCBMNONZLJZPABQDRAUERSEUCUDUFFGHTABCDU
  AUB $.
$}
 

  ${
  $d A x $.
  $d D x $.
  $d t_0 x $.
	bl.tsoi.1 $e |- ( A e. ZZ /\ A <_ 0 ) $.
	bl.tsoi.2 $e |- ( D e. RR /\ 0 < D ) $.
	bl.tsoi.3 $e |- t_0 e. TIME  $.
	bl.tsoi.4 $e |- 0 <_ ( t_0 + ( D x. A ) ) $. 
$( Time-shift offset (inference) for converting ` ^. ` into @ $)  
bl.tsoi $p |- ( t_0 + ( D x. A ) ) e. TIME 
	$= ( vx co wcel cr cc0 cle wbr cnow wsbc wa ax-mp pm3.2i mpbir cmul
  cv caddc w3a bl.etir clt simpli cz zre remulcl readdcl sbcel1v
  sbcbr2g ctime csb wb eqid wceq csbvarg breq12i bitri wo simpri wi
  ltle olci mulle0b leadd2i mpbi readdrid breqtri bl.etiamn
  df-bl.nowrr sbcbr1g 0re letri 3pm3.2i sbc3an cab clelab df-bl.time
  eleq2i sbc5 3bitr4i wex ) CBAUAIZUCIZUNJZHUBZKJZLWIMNZWIOMNZUDZHWGP
  ZWNWJHWGPZWKHWGPZWLHWGPZUDWOWPWQWOWGKJZCKJZWFKJZQWRWSWTCUNJZWSFCUER
  ZBKJZAKJZQZWTXCXDXCLBUFNZEUGZAUHJZXDXHALMNZDUGAUIRSZBAUJRZSCWFUKRZH
  WGKULTWPLWGMNZGWPLHWGWIUOZMNZXMWRWPXOUPXLHWGLWIMKUMRLLXNWGMLUQWRXNW
  GURXLHWGKUSRZUTVATWQXNOMNZXQWGOMNZWGCMNZCOMNZQXRXSXTWGCLUCIZCMWFLMN
  ZWGYAMNYBBLMNLAMNQZLBMNZXIQZVBZYEYCYDXIXFYDXCXFEVCLKJZXCQXFYDVDYGXC
  VOXGSLBVERRXHXIDVCSVFXEYBYFUPXJBAVGRTWFLCXKVOXBVHVIWSYACURXBCVJRVKX
  AXTFCVLRSWGCOXLXBOKJLOMNVMUGVPRXNWGOOMXPOUQUTTWRWQXQUPXLHWGWIOMKVNR
  TVQWJWKWLHWGVRTWGWMHVSZJWIWGURWMQHWEWHWNWMHWGVTUNYHWGHWAWBWMHWGWCWD
  T $.
  $}
 
 
  ${
  bl.ts0.1 $e |- t_0 e. TIME $. 
  bl.ts0.2 $e |- ( D e. RR /\ 0 < D ) $. 
$( Time-shift Introduction: unspecified time-shift is 0 $)
bl.ts0 $p |- boldI [[ ( ph <-> ( ph ^. 0 ) ) , t_0 ]]
	$= ( cc0 wts wb wboldit cmul co caddc ctime wcel w3a cr ax-mp
  mpbir wceq 3pm3.2i biid eqid clt wbr simpli remul01 bl.rt sselii
  readdrid oveq12i eqtri eleq1i eqcomi ax-bl.bi mpbi cz pm3.2i
  df-bl.ts bitr4i wa 0z df-bl.bit ) AAFGZHCIACIZVCCIZHVDACBFJKZLKZIZVEAA
  HZVDVHHZAUACMNZVGMNZCVGSZOVIVJHVKVLVMDVLVKDVGCMVGCFLKZCCCVFFLCUBBPN
  ZVFFSVOFBUCUDEUEZBUFQUJCPNVNCSMPCUGDUHCUIQUKZULRZVGCVQUMTAACVGUNQUO
  FUPNZVOVKVLOZUTVEVHHVSVTVAVOVKVLVPDVRTUQAFBCURQUSAVCCDVBR $.
  $}
 
  ${
  bl.tsc0.1 $e |- t_0 e. TIME $.  
  bl.tsc0.2 $e |- ( D e. RR /\ 0 < D ) $. 
$( Time-shift Introduction: unspecified time-shift is 0 $)
bl.tsc0 $p |- boldI [[ A = ( A ^. 0 ) , t_0 ]]
	$= ( cc0 clats wceq wboldit wboldict co caddc eqid ctime wcel
  w3a cr ax-mp mpbir 3pm3.2i cmul wb clt wbr simpli remul01 oveq12i
  bl.rt sselii readdrid eqtri eleq1i eqcomi ax-bl.eq cz wa pm3.2i
  df-bl.tsc mpbi 0z eqtr4i df-bl.eqt ) AAFGZHCIACJZVCCJZHVDACBFUAKZLKZJZ
  VEAAHZVDVHHZAMCNOZVGNOZCVGHZPVIVJUBVKVLVMDVLVKDVGCNVGCFLKZCCCVFFLCM
  BQOZVFFHVOFBUCUDEUEZBUFRUGCQOVNCHNQCUHDUICUJRUKZULSZVGCVQUMTAACVGUN
  RUSFUOOZVOVKVLPZUPVEVHHVSVTUTVOVKVLVPDVRTUQAFBCURRVAAVCCDVBS $.
  $}


$( Compose ` ^. `  over predicate. $)
$( bl.tscom $p |- ( ( ( A e. ZZ /\ B e. ZZ /\ ( A + B ) <_ 0 ) /\ ( D e. RR /\ 0 < D ) /\
			( t_0 e. TIME /\ ( t_0 + ( D x. ( A + B ) ) ) e. TIME ) ) -> 
  boldI [[ ( ( ( ph ^. A ) ^. B ) <-> ( ph ^. ( A + B ) ) , t_0 ]] ) ) 
  $= ? $.
$)

$( Compose ` ^. `  over value. $)
$( bl.tscomc $p |- ( ( ( B e. ZZ /\ C e. ZZ /\ ( B + C ) <_ 0 ) /\ ( D e. RR /\ 0 < D ) /\
			( t_0 e. TIME /\  ( t_0 + ( D x. ( B + C ) ) ) e. TIME ) ) -> 
  boldI [[ ( ( A ^. B ) ^. C ) = ( A ^. ( B + C ) ) , t_0 ]] ) 
  $= ? $.
$) 

  ${
  bl.tscomi.1 $e |- ( A e. ZZ /\ B e. ZZ ) $.
  bl.tscomi.2 $e |- D e. RR $.
  bl.tscomi.3 $e |- t_0 e. TIME $.
  bl.tscomi.4 $e |- ( t_0 + ( D x. ( A + B ) ) ) e. TIME $.	  
  bl.tscomi.5 $e |- ( t_0 + ( D x. B ) ) e. TIME $.	  
$( Compose ` ^. `  over predicate, inference. $)
bl.tscomi $p |- boldI [[ ( ( ( ph ^. A ) ^. B ) <-> ( ph ^. ( A + B ) ) ) , t_0 ]] 
  $= ( wts caddc co wb wboldit wcel ctime cr ax-mp cc cmul simpri
  zre bl.tsi simpli bl.adddii addcomgi eqtri oveq2i bl.etir recn mp2b
  zcn mulcli addassi eqtr4i eqcomi eqeltri biid wceq w3a 3pm3.2i
  ax-bl.bi cz mpbi 3bitri wa pm3.2i zaddcl bitr4i df-bl.bit mpbir ) ABKZ
  CKZABCLMZKZNEOVNEOZVPEOZNVQAEDVOUAMZLMZOZVRVQVMEDCUAMZLMZOAWCDBUAMZ
  LMZOZWAVMCDEBVDPZCVDPZFUBZGHJUDABDWCWGWHFUEZGJWEVTQVTWEVTEWBWDLMZLM
  WEVSWKELVSWDWBLMWKDBCGWGBRPWJBUCSWHCRPWICUCSUFWDWBUGUHUIEWBWDEQPERP
  ETPHEUJEUKULDCDRPDTPGDUKSZWHCTPWICUMSUNDBWLWGBTPWJBUMSUNUOUPUQZIURZ
  UDAANZWFWANZAUSWEQPZVTQPZWEVTUTZVAWOWPNWQWRWSWNIWMVBAAWEVTVCSVEVFAV
  ODEWGWHVGVOVDPWGWHWJWIVHBCVISGHIUDVJVNVPEHVKVL $.
  $}
 
  ${
  bl.tscomci.1 $e |- ( B e. ZZ /\ C e. ZZ ) $.
  bl.tscomci.2 $e |-  D e. RR $.
  bl.tscomci.3 $e |- t_0 e. TIME $.
  bl.tscomci.4 $e |- ( t_0 + ( D x. ( B + C ) ) ) e. TIME $.	  
  bl.tscomci.5 $e |- ( t_0 + ( D x. C ) ) e. TIME $.	  
$( Compose ` ^. `  over value, inference. $)
bl.tscomci $p |- boldI [[ ( ( A ^. B ) ^. C ) = ( A ^. ( B + C ) ) , t_0 ]] 
  $= ( clats caddc co wceq wboldict wcel ctime cr ax-mp cc cmul
  simpri wboldit bl.tsci simpli zre bl.adddii addcomgi eqtri
  bl.etir recn cz oveq2i mp2b zcn mulcli addassi eqtr4i eqcomi
  eqeltri eqid w3a wb 3pm3.2i ax-bl.eq mpbi 3eqtri wa pm3.2i zaddcl
  df-bl.eqt mpbir ) ABKZCKZABCLMZKZNEUCVNEOZVPEOZNVQAEDVOUAMZLMZOZVRVQVM
  EDCUAMZLMZOAWCDBUAMZLMZOZWAVMCDEBULPZCULPZFUBZGHJUDABDWCWGWHFUEZGJW
  EVTQVTWEVTEWBWDLMZLMWEVSWKELVSWDWBLMWKDBCGWGBRPWJBUFSWHCRPWICUFSUGW
  DWBUHUIUMEWBWDEQPERPETPHEUJEUKUNDCDRPDTPGDUKSZWHCTPWICUOSUPDBWLWGBT
  PWJBUOSUPUQURUSZIUTZUDAANZWFWANZAVAWEQPZVTQPZWEVTNZVBWOWPVCWQWRWSWN
  IWMVDAAWEVTVESVFVGAVODEWGWHVHVOULPWGWHWJWIVIBCVJSGHIUDURVNVPEHVKVL
  $.
  $}
 

  ${
  bl.tsbii.1 $e |- ( A e. ZZ /\ B e. ZZ ) $.
  bl.tsbii.2 $e |- ( D e. RR /\ 0 < D ) $.
  bl.tsbii.3 $e |- t_0 e. TIME $.
  bl.tsbii.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  bl.tsbii.5 $e |- ( t_0 + ( D x. B ) ) e. TIME $.	
  bl.tsbii.6 $e |- ( ph <-> ps ) $.	
  bl.tsbii.7 $e |- A = B  $.	
$( Equivalence (biconditional) of ` ^. ` for predicates, inference. $)
bl.tsbii $p |- boldI [[ ( ( ph ^. A ) <-> ( ps ^. B ) ) , t_0 ]]
  $= ( wb wboldit cmul co wcel cc ax-mp wts caddc wceq w3a cc0 wne
  wa ctime cz simpli zsscn sseli simpri cr clt wbr ax-resscn 0re
  3pm3.2i ltnei pm3.2i mulcan2 mpbir mulcomi 3eqtr3i oveq2i ax-bl.bi
  df-bl.ts mpbi 3bitr4i df-bl.bit ) ACUAZBDUAZNFOVLFOZVMFOZNAFECPQZUB
  QZOZBFEDPQZUBQZOZVNVOABNZVRWANZLVQUHRZVTUHRZVQVTUCZUDWBWCNWDWEWFJKV
  PVSFUBCEPQZDEPQZVPVSWGWHUCZCDUCZMCSRZDSRZESRZEUEUFZUGZUDWIWJNWKWLWO
  CUIRZWKWPDUIRZGUJZUISCUKULTZWQWLWPWQGUMZUISDUKULTZWMWNEUNRZWMXBUEEU
  OUPZHUJZUNSEUQULTZXCWNXBXCHUMUEEURXDUTTVAUSCDEVBTVCCEWSXEVDDEXAXEVD
  VEVFUSABVQVTVGTVIWPXBFUHRZWDUDZUGVNVRNWPXGWRXBXFWDXDIJUSVAACEFVHTWQ
  XBXFWEUDZUGVOWANWQXHWTXBXFWEXDIKUSVABDEFVHTVJVLVMFIVKVC $.
  $} 

  ${
  bl.tseqi.1 $e |- ( A e. ZZ /\ B e. ZZ ) $.
  bl.tseqi.2 $e |- ( D e. RR /\ 0 < D ) $.
  bl.tseqi.3 $e |- t_0 e. TIME $.
  bl.tseqi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  bl.tseqi.5 $e |- ( t_0 + ( D x. B ) ) e. TIME $.
  bl.tseqi.6 $e |- ( C e. RR /\ E e. RR	) $.
  bl.tseqi.7 $e |- ( C = E /\ A = B ) $.
$( Equality of ` ^. ` for values, inference. $)
bl.tseqi $p |- boldI [[ ( C ^. A ) = ( E ^. B ) , t_0 ]] 
  $= ( wceq wboldict cmul co wcel cc ax-mp clats wboldit simpli
  w3a caddc ctime wb simpri cc0 wne wa cz zsscn sseli clt ax-resscn
  ltnei cr wbr pm3.2i 3pm3.2i mulcan2 mpbir mulcomi 3eqtr3i oveq2i
  ax-bl.eq 0re mpbi df-bl.tsc 3eqtr4i df-bl.eqt ) CAUAZEBUAZNFUBVMFOZ
  VNFOZNCFDAPQZUEQZOZEFDBPQZUEQZOZVOVPCENZVSWBNZWCABNZMUCVRUFRZWAUFRZ
  VRWANZUDWCWDUGWFWGWHJKVQVTFUEADPQZBDPQZVQVTWIWJNZWEWCWEMUHASRZBSRZD
  SRZDUIUJZUKZUDWKWEUGWLWMWPAULRZWLWQBULRZGUCZULSAUMUNTZWRWMWQWRGUHZU
  LSBUMUNTZWNWODURRZWNXCUIDUOUSZHUCZURSDUPUNTZXDWOXCXDHUHUIDVHXEUQTUT
  VAABDVBTVCADWTXFVDBDXBXFVDVEVFVACEVRWAVGTVIWQXCFUFRZWFUDZUKVOVSNWQX
  HWSXCXGWFXEIJVAUTCADFVJTWRXCXGWGUDZUKVPWBNWRXIXAXCXGWGXEIKVAUTEBDFV
  JTVKVMVNFIVLVC $.
  $} 
 
$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Distribute Time-Shift Temporal Operator ` ^. `
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(  ***** Distribute ` ^. ` over logic *****  $)
 
${
  bl.tsan2i.1 $e |- A e. ZZ $.
  bl.tsan2i.2 $e |- D e. RR $.
  bl.tsan2i.3 $e |- t_0 e. TIME $.
  bl.tsan2i.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over conjunction, two terms,inference $)
bl.tsan2i $p |- boldI [[ ( ( ( ph /\ ps ) ^. A ) 
      <-> ( ( ph ^. A ) /\ ( ps ^. A ) ) ) , t_0 ]]  
  $= ( wa wts wb wboldit cmul caddc df-bl.ant bl.tsi anbi12i 3bitr4i
  co bitr4i df-bl.bit mpbir ) ABJZCKZACKZBCKZJZLEMUEEMZUHEMZLUIUFEMZU
  GEMZJZUJUDEDCNTOTZMAUNMZBUNMZJUIUMABUNIPUDCDEFGHIQUKUOULUPACDEFGHIQ
  BCDEFGHIQRSUFUGEHPUAUEUHEHUBUC $.
	$}
 
  ${
  bl.tsan3i.1 $e |- A e. ZZ $.
  bl.tsan3i.2 $e |- ( D e. RR /\ 0 < D ) $.
  bl.tsan3i.3 $e |- t_0 e. TIME $.
  bl.tsan3i.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over conjunction, three terms, inference $)
bl.tsan3i $p |- boldI [[ ( ( ( ph /\ ps /\ ch ) ^. A ) <-> 
    ( ( ph ^. A ) /\ ( ps ^. A ) /\ ( ch ^. A ) ) ) , t_0 ]]
  $= ( w3a wts wb wboldit co wa wcel bl.tsi bitri bitr4i caddc cr
  cc0 cmul clt wbr simpli df-3an ctime wceq eqid ax-bl.bi ax-mp
  df-bl.ant 3pm3.2i mpbi anbi1i 3anbi123i bl.an3t df-bl.bit mpbir ) A
  BCKZDLZADLZBDLZCDLZKZMFNVCFNZVGFNZMVHVDFNZVEFNZVFFNZKZVIVHAFEDUDOUA
  OZNZBVNNZCVNNZKZVMVHVOVPPZVQPZVRVHABPZVNNZVQPZVTVHWACPZVNNZWCVHVBVN
  NZWEVBDEFGEUBQUCEUEUFHUGZIJRVBWDMZWFWEMZABCUHVNUIQZWJVNVNUJZKWHWIMW
  JWJWKJJVNUKUOVBWDVNVNULUMUPSWACVNJUNSWBVSVQABVNJUNUQSVOVPVQUHTVJVOV
  KVPVLVQADEFGWGIJRBDEFGWGIJRCDEFGWGIJRURTVDVEVFFIUSTVCVGFIUTVA $.
  $}

  ${
  bl.tsan3ri.1 $e |- A e. ZZ $.
  bl.tsan3ri.2 $e |- D e. RR $.
  bl.tsan3ri.3 $e |- t_0 e. TIME $.
  bl.tsan3ri.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over conjunction, three terms (right), inference. $)
bl.tsan3ri $p |- boldI [[ ( ( ( ph /\ ( ps /\ ch ) ) ^. A ) <-> 
    ( ( ph ^. A ) /\ ( ( ps ^. A ) /\ ( ch ^. A ) ) ) ) , t_0 ]]
  $= ( wa wts wb wboldit co bl.tsi df-bl.ant anbi2i anbi12i bitr4i
  cmul caddc 3bitri df-bl.bit mpbir ) ABCKZKZDLZADLZBDLZCDLZKZKZMFNUHFNZ
  UMFNZMUNUIFNZULFNZKZUOUNUPUJFNZUKFNZKZKZURUNAFEDUAOUBOZNZBVCNZCVCNZ
  KZKZVBUNUGVCNVDUFVCNZKVHUGDEFGHIJPAUFVCJQVIVGVDBCVCJQRUCUPVDVAVGADE
  FGHIJPUSVEUTVFBDEFGHIJPCDEFGHIJPSSTUQVAUPUJUKFIQRTUIULFIQTUHUMFIUDU
  E $.
  $}


  ${
  bl.tsan3li.1 $e |- A e. ZZ $.
  bl.tsan3li.2 $e |- D e. RR $.
  bl.tsan3li.3 $e |- t_0 e. TIME $.
  bl.tsan3li.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over conjunction, three terms (left), inference. $)
bl.tsan3li $p |- boldI [[ ( ( ( ( ph /\ ps ) /\ ch ) ^. A ) <-> 
    ( ( ( ph ^. A ) /\ ( ps ^. A ) ) /\ ( ch ^. A ) ) ) , t_0 ]]
$= ( wa wts wb wboldit df-bl.ant anbi1i cmul co bl.tsi anbi12i
  caddc 3bitri bitr4i 3bitr4ri df-bl.bit mpbir ) ABKZCKZDLZADLZBDLZKZ
  CDLZKZMFNUIFNZUNFNZMULFNZUMFNZKUJFNZUKFNZKZURKZUPUOUQVAURUJUKFIOPUL
  UMFIOUOAFEDQRUARZNZBVCNZKZCVCNZKZVBUOUHVCNUGVCNZVGKVHUHDEFGHIJSUGCV
  CJOVIVFVGABVCJOPUBVAVFURVGUSVDUTVEADEFGHIJSBDEFGHIJSTCDEFGHIJSTUCUD
  UIUNFIUEUF $.
  $}

  ${
  bl.tsani.1 $e |- A e. ZZ $.
  bl.tsani.2 $e |- ( D e. RR /\ 0 < D ) $.
  bl.tsani.3 $e |- t_0 e. TIME $.
  bl.tsani.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over conjunction, wff-list , inference. $)
bl.tsani $p |- boldI [[ ( ( /\( l_ l2 )x ^. A ) <-> 
    ( ( /\( l_ )x ^. A ) /\ ( /\( l2 )x ^. A ) ) ) , t_0 ]]
  $= ( wfl2 wland wts wa cz wcel pm4.24 mpbi df-bl.lan2wl eqid bl.tsbii
  cr cc0 clt wbr simpli bl.tsan2i bl.bitrit ) CDJKZALCKZDKZMZALUIALUJ
  ALMEHUHUKAABEANOZULULMFULPQGHIICDRASTUIUJABEFBUAOUBBUCUDGUEHIUFUG
  $.
  $}

 
${
  bl.tsor2i.1 $e |- A e. ZZ $.
  bl.tsor2i.2 $e |- D e. RR $.
  bl.tsor2i.3 $e |- t_0 e. TIME $.
  bl.tsor2i.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over disjunction, two terms,inference $)
bl.tsor2i $p |- boldI [[ ( ( ( ph \/ ps ) ^. A ) 
      <-> ( ( ph ^. A ) \/ ( ps ^. A ) ) ) , t_0 ]]  
  $= ( wo wts wb wboldit cmul caddc df-bl.ort bl.tsi orbi12i 3bitr4i
  co bitr4i df-bl.bit mpbir ) ABJZCKZACKZBCKZJZLEMUEEMZUHEMZLUIUFEMZU
  GEMZJZUJUDEDCNTOTZMAUNMZBUNMZJUIUMABUNIPUDCDEFGHIQUKUOULUPACDEFGHIQ
  BCDEFGHIQRSUFUGEHPUAUEUHEHUBUC $.
	$}
 
  ${
  bl.tsor3i.1 $e |- A e. ZZ $.
  bl.tsor3i.2 $e |- D e. RR $.
  bl.tsor3i.3 $e |- t_0 e. TIME $.
  bl.tsor3i.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over disjunction, three terms, inference $)
bl.tsor3i $p |- boldI [[ ( ( ( ph \/ ps \/ ch ) ^. A ) <-> 
    ( ( ph ^. A ) \/ ( ps ^. A ) \/ ( ch ^. A ) ) ) , t_0 ]]
  $= ( w3o wts wb wboldit co wo bl.tsi df-3or bitri bitr4i cmul
  caddc ctime wcel wceq w3a eqid 3pm3.2i ax-bl.bi ax-mp df-bl.ort
  3orbi123i mpbi orbi1i bl.or3t df-bl.bit mpbir ) ABCKZDLZADLZBDLZCDL
  ZKZMFNUSFNZVCFNZMVDUTFNZVAFNZVBFNZKZVEVDAFEDUAOUBOZNZBVJNZCVJNZKZVI
  VDVKVLPZVMPZVNVDABPZVJNZVMPZVPVDVQCPZVJNZVSVDURVJNZWAURDEFGHIJQURVT
  MZWBWAMZABCRVJUCUDZWEVJVJUEZUFWCWDMWEWEWFJJVJUGUHURVTVJVJUIUJUMSVQC
  VJJUKSVRVOVMABVJJUKUNSVKVLVMRTVFVKVGVLVHVMADEFGHIJQBDEFGHIJQCDEFGHI
  JQULTUTVAVBFIUOTUSVCFIUPUQ $.
  $}

  ${
  bl.tsor3ri.1 $e |- A e. ZZ $.
  bl.tsor3ri.2 $e |- D e. RR $.
  bl.tsor3ri.3 $e |- t_0 e. TIME $.
  bl.tsor3ri.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over disjunction, three terms (right), inference. $)
bl.tsor3ri $p |- boldI [[ ( ( ( ph \/ ( ps \/ ch ) ) ^. A ) <-> 
    ( ( ph ^. A ) \/ ( ( ps ^. A ) \/ ( ch ^. A ) ) ) ) , t_0 ]]
  $= ( wo wts wb wboldit df-bl.ort orbi2i cmul co bl.tsi orbi12i
  caddc 3bitri bitr4i 3bitr4ri df-bl.bit mpbir ) ABCKZKZDLZADLZBDLZCD
  LZKZKZMFNUIFNZUNFNZMUJFNZUMFNZKUQUKFNZULFNZKZKZUPUOURVAUQUKULFIOPUJ
  UMFIOUOAFEDQRUARZNZBVCNZCVCNZKZKZVBUOUHVCNVDUGVCNZKVHUHDEFGHIJSAUGV
  CJOVIVGVDBCVCJOPUBUQVDVAVGADEFGHIJSUSVEUTVFBDEFGHIJSCDEFGHIJSTTUCUD
  UIUNFIUEUF $.
  $}


  ${
  bl.tsor3li.1 $e |- A e. ZZ $.
  bl.tsor3li.2 $e |- D e. RR $.
  bl.tsor3li.3 $e |- t_0 e. TIME $.
  bl.tsor3li.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over disjunction, three terms (left), inference. $)
bl.tsor3li $p |- boldI [[ ( ( ( ( ph \/ ps ) \/ ch  ) ^. A ) <-> 
    ( ( ( ph ^. A ) \/ ( ps ^. A ) ) \/ ( ch ^. A ) ) ) , t_0 ]]
  $= ( wo wts wb wboldit df-bl.ort orbi1i cmul co bl.tsi orbi12i
  caddc 3bitri bitr4i 3bitr4ri df-bl.bit mpbir ) ABKZCKZDLZADLZBDLZKZ
  CDLZKZMFNUIFNZUNFNZMULFNZUMFNZKUJFNZUKFNZKZURKZUPUOUQVAURUJUKFIOPUL
  UMFIOUOAFEDQRUARZNZBVCNZKZCVCNZKZVBUOUHVCNUGVCNZVGKVHUHDEFGHIJSUGCV
  CJOVIVFVGABVCJOPUBVAVFURVGUSVDUTVEADEFGHIJSBDEFGHIJSTCDEFGHIJSTUCUD
  UIUNFIUEUF $.
  $}

  ${
  bl.tsori.1 $e |- A e. ZZ $.
  bl.tsori.2 $e |- ( D e. RR /\ 0 < D ) $.
  bl.tsori.3 $e |- t_0 e. TIME $.
  bl.tsori.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over disjunction, wff-list, inference. $)
bl.tsori $p |- boldI [[ ( ( \/( l_ l2 )x ^. A ) <-> 
    ( ( \/( l_ )x ^. A ) \/ ( \/( l2 )x ^. A ) ) ) , t_0 ]]
  $= ( wfl2 wlo wts wo cz wcel wa pm4.24 mpbi df-bl.lor2wl eqid
  bl.tsbii cr cc0 clt wbr simpli bl.tsor2i bl.bitrit ) CDJKZALCKZDKZM
  ZALUJALUKALMEHUIULAABEANOZUMUMPFUMQRGHIICDSATUAUJUKABEFBUBOUCBUDUEG
  UFHIUGUH $.
  $}


$(  ***** Distribute ` ^. ` over arithmetic *****  $)
 
  ${
  bl.tsad2i.1 $e |- A e. ZZ $.
  bl.tsad2i.2 $e |- D e. RR $.
  bl.tsad2i.3 $e |- t_0 e. TIME $.
  bl.tsad2i.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over addition, two terms, inference. $)
bl.tsad2i $p |- boldI [[ ( ( C + B ) ^. A ) =
		( ( C ^. A ) + ( B ^. A ) ) , t_0 ]]
  $= ( caddc co clats wceq wboldit wboldict cmul df-bl.addt
  bl.tsci oveq12i 3eqtr4i eqtr4i df-bl.eqt mpbir ) CBJKZALZCALZBALZJK
  ZMENUEEOZUHEOZMUIUFEOZUGEOZJKZUJUDEDAPKJKZOCUNOZBUNOZJKUIUMCBUNIQUD
  ADEFGHIRUKUOULUPJCADEFGHIRBADEFGHIRSTUFUGEHQUAUEUHEHUBUC $.
  $}

  ${
  bl.tsad3ri.1 $e |- A e. ZZ $.
  bl.tsad3ri.2 $e |- D e. RR $.
  bl.tsad3ri.3 $e |- t_0 e. TIME $.
  bl.tsad3ri.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tsad3ri.5 $e |- ( C e. RR /\ E e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over addition, three terms (right), inference. $)
bl.tsad3ri $p |- boldI [[ ( ( C + ( E + B ) ) ^. A ) =
		( ( C ^. A ) + ( ( E ^. A ) + ( B ^. A ) ) ) , t_0 ]]
  $= ( co clats wceq wboldict bl.tsci df-bl.addt oveq2i oveq12i
  eqtr4i caddc wboldit cmul 3eqtri df-bl.eqt mpbir ) CEBTKZTKZALZC
  ALZEALZBALZTKZTKZMFUAUHFNZUMFNZMUNUIFNZULFNZTKZUOUNUPUJFNZUKFNZTKZT
  KZURUNCFDAUBKTKZNZEVCNZBVCNZTKZTKZVBUNUGVCNVDUFVCNZTKVHUGADFGHIJOCU
  FVCJPVIVGVDTEBVCJPQUCUPVDVAVGTCADFGHIJOUSVEUTVFTEADFGHIJOBADFGHIJOR
  RSUQVAUPTUJUKFIPQSUIULFIPSUHUMFIUDUE $.
  $}

  ${
  bl.tsad3li.1 $e |- A e. ZZ $.
  bl.tsad3li.2 $e |- D e. RR $.
  bl.tsad3li.3 $e |- t_0 e. TIME $.
  bl.tsad3li.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tsad3li.5 $e |- ( C e. RR /\ E e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over addition, three terms (left), inference. $)
bl.tsad3li $p |- boldI [[ ( ( ( C + E ) + B ) ^. A ) =
		( ( ( C ^. A ) + ( E ^. A ) ) + ( B ^. A ) ) , t_0 ]]
  $= ( co clats wceq wboldict bl.tsci df-bl.addt oveq1i oveq12i
  eqtr4i caddc wboldit cmul 3eqtri df-bl.eqt mpbir ) CETKZBTKZALZC
  ALZEALZTKZBALZTKZMFUAUHFNZUMFNZMUNUKFNZULFNZTKZUOUNUIFNZUJFNZTKZUQT
  KZURUNCFDAUBKTKZNZEVCNZTKZBVCNZTKZVBUNUGVCNUFVCNZVGTKVHUGADFGHIJOUF
  BVCJPVIVFVGTCEVCJPQUCVAVFUQVGTUSVDUTVETCADFGHIJOEADFGHIJORBADFGHIJO
  RSUPVAUQTUIUJFIPQSUKULFIPSUHUMFIUDUE $.
  $}
 
  ${
  bl.tsadi.1 $e |- A e. ZZ $.
  bl.tsadi.2 $e |- D e. RR $.
  bl.tsadi.3 $e |- t_0 e. TIME $.
  bl.tsadi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tsadi.5 $e |- ( +( cl_1 )x  e. RR /\ +( cl_2 )x  e. RR ) $. $)
$( Distribute ` ^. ` over addition, class-list, inference. $)
bl.tsadi $p |- boldI [[ ( (  +( cl_1 )x + +( cl_2 )x  ) ^. A ) =
		( ( +( cl_1 )x ^. A ) + ( +( cl_2 )x  ^. A ) ) , t_0 ]]
  $= ( bl.cadd bl.tsad2i ) ADJCJBEFGHIK $.
  $}

  ${
  bl.tssubi.1 $e |- A e. ZZ $.
  bl.tssubi.2 $e |- D e. RR $.
  bl.tssubi.3 $e |- t_0 e. TIME $.
  bl.tssubi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tssubi.5 $e |- ( C e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over subtraction, inference. $)
bl.tssubi $p |- boldI [[ ( ( C - B ) ^. A ) =
		( ( C ^. A ) - ( B ^. A ) ) , t_0 ]]
  $= ( cmin co clats wceq wboldit wboldict caddc df-bl.subt
  bl.tsci cmul oveq12i 3eqtr4i eqtr4i df-bl.eqt mpbir ) CBJKZALZCALZB
  ALZJKZMENUFEOZUIEOZMUJUGEOZUHEOZJKZUKUEEDASKPKZOCUOOZBUOOZJKUJUNCBU
  OIQUEADEFGHIRULUPUMUQJCADEFGHIRBADEFGHIRTUAUGUHEHQUBUFUIEHUCUD $.
  $}

  ${
  bl.tsmul2i.1 $e |- A e. ZZ $.
  bl.tsmul2i.2 $e |- D e. RR $.
  bl.tsmul2i.3 $e |- t_0 e. TIME $.
  bl.tsmul2i.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tsmul2i.5 $e |- ( C e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over multiplication, two terms, inference. $)
bl.tsmul2i $p |- boldI [[ ( ( C x. B ) ^. A ) =
		( ( C ^. A ) x. ( B ^. A ) ) , t_0 ]]
  $= ( cmul co clats wceq wboldit wboldict caddc df-bl.mult
  bl.tsci oveq12i 3eqtr4i eqtr4i df-bl.eqt mpbir ) CBJKZALZCALZBALZJK
  ZMENUEEOZUHEOZMUIUFEOZUGEOZJKZUJUDEDAJKPKZOCUNOZBUNOZJKUIUMCBUNIQUD
  ADEFGHIRUKUOULUPJCADEFGHIRBADEFGHIRSTUFUGEHQUAUEUHEHUBUC $.
  $}

  ${
  bl.tsmul3ri.1 $e |- A e. ZZ $.
  bl.tsmul3ri.2 $e |- D e. RR $.
  bl.tsmul3ri.3 $e |- t_0 e. TIME $.
  bl.tsmul3ri.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tsmul3ri.5 $e |- ( C e. RR /\ E e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over multiplication, three terms (right), inference. $)
bl.tsmul3ri $p |- boldI [[ ( ( C x. ( E x. B ) ) ^. A ) =
		( ( C ^. A ) x. ( ( E ^. A ) x. ( B ^. A ) ) ) , t_0 ]]
  $= ( cmul co clats wboldict bl.tsci df-bl.mult oveq2i oveq12i
  eqtr4i wceq wboldit caddc 3eqtri df-bl.eqt mpbir ) CEBKLZKLZAMZC
  AMZEAMZBAMZKLZKLZTFUAUHFNZUMFNZTUNUIFNZULFNZKLZUOUNUPUJFNZUKFNZKLZK
  LZURUNCFDAKLUBLZNZEVCNZBVCNZKLZKLZVBUNUGVCNVDUFVCNZKLVHUGADFGHIJOCU
  FVCJPVIVGVDKEBVCJPQUCUPVDVAVGKCADFGHIJOUSVEUTVFKEADFGHIJOBADFGHIJOR
  RSUQVAUPKUJUKFIPQSUIULFIPSUHUMFIUDUE $.
  $}

  ${
  bl.tsmul3li.1 $e |- A e. ZZ $.
  bl.tsmul3li.2 $e |- D e. RR $.
  bl.tsmul3li.3 $e |- t_0 e. TIME $.
  bl.tsmul3li.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tsmul3li.5 $e |- ( C e. RR /\ E e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over multiplication, three terms (left), inference. $)
bl.tsmul3li $p |- boldI [[ ( ( ( C x. E ) x. B ) ^. A ) =
		( ( ( C ^. A ) x. ( E ^. A ) ) x. ( B ^. A ) ) , t_0 ]]
  $= ( cmul co clats wboldict bl.tsci df-bl.mult oveq1i oveq12i
  eqtr4i wceq wboldit caddc 3eqtri df-bl.eqt mpbir ) CEKLZBKLZAMZC
  AMZEAMZKLZBAMZKLZTFUAUHFNZUMFNZTUNUKFNZULFNZKLZUOUNUIFNZUJFNZKLZUQK
  LZURUNCFDAKLUBLZNZEVCNZKLZBVCNZKLZVBUNUGVCNUFVCNZVGKLVHUGADFGHIJOUF
  BVCJPVIVFVGKCEVCJPQUCVAVFUQVGKUSVDUTVEKCADFGHIJOEADFGHIJORBADFGHIJO
  RSUPVAUQKUIUJFIPQSUKULFIPSUHUMFIUDUE $.
  $}
 
  ${
  bl.tsmuli.1 $e |- A e. ZZ $.
  bl.tsmuli.2 $e |- D e. RR $.
  bl.tsmuli.3 $e |- t_0 e. TIME $.
  bl.tsmuli.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tsmuli.5 $e |- ( +( cl_1 )x  e. RR /\ +( cl_2 )x  e. RR ) $. $)
$( Distribute ` ^. ` over multiplication, class-list, inference. $)
bl.tsmuli $p |- boldI [[ ( (  +( cl_1 )x x. +( cl_2 )x  ) ^. A ) =
		( ( +( cl_1 )x ^. A ) x. ( +( cl_2 )x  ^. A ) ) , t_0 ]]
  $= ( bl.cadd bl.tsmul2i ) ADJCJBEFGHIK $.
  $}
 
  ${
  bl.tsdivi.1 $e |- A e. ZZ $.
  bl.tsdivi.2 $e |- D e. RR $.
  bl.tsdivi.3 $e |- t_0 e. TIME $.
  bl.tsdivi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$(  bl.tsdivi.5 $e |- ( C e. RR /\ B e. RR ) $.  $)
$( Distribute ` ^. ` over division, inference. $)
bl.tsdivi $p |- boldI [[ ( ( C / B ) ^. A ) = ( ( C ^. A ) / ( B ^. A ) ) , t_0 ]]
  $= ( cdiv co clats wceq wboldit wboldict caddc df-bl.divt
  bl.tsci cmul oveq12i 3eqtr4i eqtr4i df-bl.eqt mpbir ) CBJKZALZCALZB
  ALZJKZMENUFEOZUIEOZMUJUGEOZUHEOZJKZUKUEEDASKPKZOCUOOZBUOOZJKUJUNCBU
  OIQUEADEFGHIRULUPUMUQJCADEFGHIRBADEFGHIRTUAUGUHEHQUBUFUIEHUCUD $.
  $}

  ${
  bl.tsumi.1 $e |- A e. ZZ $.
  bl.tsumi.2 $e |- D e. RR $.
  bl.tsumi.3 $e |- t_0 e. TIME $.
  bl.tsumi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
$( Distribute ` ^. ` over unary minus, inference. $)
bl.tsumi $p |- boldI [[ ( -u B  ^. A ) = -u ( B ^. A ) , t_0 ]]
  $= ( cneg clats wceq wboldit wboldict cmul caddc df-bl.umt
  negeqi co bl.tsci 3eqtr4i eqtr4i df-bl.eqt mpbir ) BIZAJZBAJZIZKDLU
  EDMZUGDMZKUHUFDMZIZUIUDDCANRORZMBULMZIUHUKBULHPUDACDEFGHSUJUMBACDEF
  GHSQTUFDGPUAUEUGDGUBUC $.
  $}


$(  ***** Distribute ^ over relations *****  $)

 
  ${
  bl.tsdeqi.1 $e |- A e. ZZ $.
  bl.tsdeqi.2 $e |- D e. RR $.
  bl.tsdeqi.3 $e |- t_0 e. TIME $.
  bl.tsdeqi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  $( bl.tsdeqi.5 $e |- ( C e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over equality, inference. $)
bl.tsdeqi $p |- boldI [[ ( ( C = B ^. A )
      <-> ( C ^. A ) = ( B ^. A ) ) , t_0 ]]
  $= ( wceq wts clats wb wboldit wboldict cmul co df-bl.eqt
  bl.tsci caddc bl.tsi eqeq12i 3bitr4i bitr4i df-bl.bit mpbir ) CBJZA
  KZCALZBALZJZMENUHENZUKENZMULUIEOZUJEOZJZUMUGEDAPQTQZNCUQOZBUQOZJULU
  PCBUQIRUGADEFGHIUAUNURUOUSCADEFGHISBADEFGHISUBUCUIUJEHRUDUHUKEHUEUF
  $.
  $}

  ${
  bl.tslti.1 $e |- A e. ZZ $.
  bl.tslti.2 $e |- D e. RR $.
  bl.tslti.3 $e |- t_0 e. TIME $.
  bl.tslti.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  $( bl.tslti.5 $e |- ( C e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over less-than, inference. $)
bl.tslti $p |- boldI [[ ( ( C < B ^. A )
      <-> ( C ^. A ) < ( B ^. A ) ) , t_0 ]]
  $= ( clt wbr wts clats wb wboldit wboldict cmul df-bl.ltt
  bl.tsci co caddc bl.tsi breq12i 3bitr4i bitr4i df-bl.bit mpbir ) CB
  JKZALZCAMZBAMZJKZNEOUIEOZULEOZNUMUJEPZUKEPZJKZUNUHEDAQTUATZOCURPZBU
  RPZJKUMUQCBURIRUHADEFGHIUBUOUSUPUTJCADEFGHISBADEFGHISUCUDUJUKEHRUEU
  IULEHUFUG $.
  $}

  ${
  bl.tsami.1 $e |- A e. ZZ $.
  bl.tsami.2 $e |- D e. RR $.
  bl.tsami.3 $e |- t_0 e. TIME $.
  bl.tsami.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  $( bl.tsami.5 $e |- ( C e. RR /\ B e. RR ) $. $)
$( Distribute ` ^. ` over at-most, inference. $)
bl.tsami $p |- boldI [[ ( ( C <_ B ^. A ) 
      <-> ( C ^. A ) <_ ( B ^. A ) ) , t_0 ]]
  $= ( cle wbr wts clats wb wboldit wboldict cmul df-bl.amt
  bl.tsci co caddc bl.tsi breq12i 3bitr4i bitr4i df-bl.bit mpbir ) CB
  JKZALZCAMZBAMZJKZNEOUIEOZULEOZNUMUJEPZUKEPZJKZUNUHEDAQTUATZOCURPZBU
  RPZJKUMUQCBURIRUHADEFGHIUBUOUSUPUTJCADEFGHISBADEFGHISUCUDUJUKEHRUEU
  IULEHUFUG $.
  $}


$(  ***** Distribute ^ over quantification *****  $)


  ${
  df-bl.tsali.1 $e |- A e. ZZ $.
  df-bl.tsali.2 $e |- D e. RR $.
  df-bl.tsali.3 $e |- t_0 e. TIME $.
  df-bl.tsali.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  df-bl.tsali.5 $e |- B e. RR $.
$( Distribute ` ^. ` over universal quantification, inference $)
df-bl.tsali $a |- boldI [[ ( ( A. x e. B ph ^. A ) 
      <-> A. x e. B ( ph ^. A ) ) , t_0 ]] $.
  $}
  
  ${
  df-bl.tsexi.1 $e |- A e. ZZ $.
  df-bl.tsexi.2 $e |- D e. RR $.
  df-bl.tsexi.3 $e |- t_0 e. TIME $.
  df-bl.tsexi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  df-bl.tsexi.5 $e |- B e. RR $.
$( Distribute ` ^. ` over existential quantification, inference $)
df-bl.tsexi $a |- boldI [[ ( ( E. x e. B ph ^. A ) 
     <-> E. x e. B ( ph ^. A ) ) , t_0 ]] $.
  $}
  
  ${
  df-bl.tssumi.1 $e |- A e. ZZ $.
  df-bl.tssumi.2 $e |- D e. RR $.
  df-bl.tssumi.3 $e |- t_0 e. TIME $.
  df-bl.tssumi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  df-bl.tssumi.5 $e |- ( B e. RR /\ C e. RR ) $.
$( Distribute ` ^. ` over summation, inference $)
df-bl.tssumi $a |- boldI [[ ( sum_ x e. B C ^. A ) 
      = sum_ x e. B ( C ^. A ) , t_0 ]] $.
  $}
  
  ${
  df-bl.tsprodi.1 $e |- A e. ZZ $.
  df-bl.tsprodi.2 $e |- D e. RR $.
  df-bl.tsprodi.3 $e |- t_0 e. TIME $.
  df-bl.tsprodi.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  df-bl.tsprodi.5 $e |- ( B e. RR /\ C e. RR ) $.
$( Distribute ` ^. ` over product, inference $)
df-bl.tsprodi $a |- boldI [[ ( prod_ x e. B C ^. A ) 
      = prod_ x e. B ( C ^. A ) , t_0 ]] $.
  $}

  ${
  df-bl.tsqq.1 $e |- A e. ZZ $.
  df-bl.tsqq.2 $e |- D e. RR $.
  df-bl.tsqq.3 $e |- t_0 e. TIME $.
  df-bl.tsqq.4 $e |- ( t_0 + ( D x. A ) ) e. TIME $.	
  df-bl.tsqq.5 $e |- ( B e. RR /\ C e. RR ) $.
$( Distribute ` ^. ` over conditional expression, inference $) 
	df-bl.tsqq $a |- boldI [[ ( if ( ph , B , C ) ^. A ) 
      = if ( ( ph ^. A ) , ( B ^. A ) , ( C ^. A ) ) , t_0 ]] $.
  $}

  
$( ********************* End of BLESS ************************ $)

$( ******************* Start of Supplemental Formal Semantics ******************* $)

$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Mererology (parthood)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( make "part" constant $)
$c part $.

$( make part variables $)
$v p_x p_y p_z $.
$( make them "part" $)
partx $f part p_x $.
party $f part p_y $.
partz $f part p_z $.


$( PartOf is constant $)
$c PartOf $.
$( p_x PartOf p_y is a wff $)
wpartof $a wff p_x PartOf p_y $.

$( Overlap is constant $)
$c Overlap $.
$( p_x Overlap p_y is a wff $)
wov $a wff p_x Overlap p_y $.

$( Underlap is constant $)
$c Underlap $.
$( p_x Underlap p_y is a wff $)
wund $a wff p_x Underlap p_y $.

$( ImproperPart is constant $)
$c ImproperPart $.
$( p_x ImproperPart p_y is a wff $)
wimp $a wff p_x ImproperPart p_y $.

$( Disjoint is constant $)
$c Disjoint $.
$( p_x Disjoint p_y is a wff $)
wpdj $a wff p_x Disjoint p_y $.

$( Atom is constant $)
$c Atom $.
$( Atom p_x is a wff $)
wpat $a wff Atom p_x $.

$( Whole is constant $)
$c Whole $.
$( Whole p_x is a wff $)
wpwh $a wff Whole p_x $.


$( Define part antireflexivity. $)
df-par $a |- -. p_x PartOf p_x $.

$( Define part transitivity. $)
df-ptr $a |- ( ( p_x PartOf p_y /\ p_y PartOf p_z ) -> p_x PartOf p_z ) $.

$( Define part overlap. $)
df-pov $a |- p_x Overlap p_y <-> E. p_z ( p_z PartOf p_x /\ p_z PartOf p_y ) $.

$( Define part underlap. $)
df-pun $a |- p_x Underlap p_y <-> E. p_z ( p_x PartOf p_z /\ p_y PartOf p_z ) $.

$( Define improper part $)
df-pim $a |- p_x ImproperPart p_y <-> ( p_x PartOf p_y \/ p_x = p_y ) $.

$( Define part disjointness $)
df-pdj $a |- p_x Disjoint p_y <-> -. p_x Overlap p_y $.

$( Define part containment hierarchy. $)
df-pch $a |- ( ( ( p_x PartOf p_y \/ p_y PartOf p_x ) \/
  ( p_x = p_y \/ p_x Disjoint p_y ) ) /\ -. ( p_x PartOf p_y /\ p_y PartOf p_x ) ) $.

$( Define atomic part. $)
df-pat $a |- Atom p_x <-> -. E. p_z ( p_z PartOf p_x ) $.

$( Define whole. $)
df-pwh $a |- Whole p_x <-> A. p_z ( p_z PartOf p_x \/ p_x = p_z ) $.

$( Part overlap is reflexive $)
povrfl $p |- p_x Overlap p_y <-> p_y Overlap p_x $= ? $.

$( Part underlap is reflexive $)
punrfl $p |- p_x Underlap p_y <-> p_y Underlap p_x $= ? $.

$( Improper part is reflexive $)
pimrfl $p |- p_x ImproperPart p_y <-> p_y ImproperPart p_x $= ? $.

$( Part disjointness is reflexive $)
pdjrfl $p |- p_x Disjoint p_y <-> p_y Disjoint p_x $= ? $.

$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Region and Location
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( make "region" constant $)
$c region $.

$( make region variables $)
$v r_0 r_1 r_2 $.
$( make them "region" $)
reg0 $f region r_0 $.
reg1 $f region r_1 $.
reg2 $f region r_2 $.

$( make "point" constant $)
$c point $.

$( make point variables $)
$v p_0 p_1 p_2 $.
$( make them "point" $)
point0 $f point p_0 $.
point1 $f point p_1 $.
point2 $f point p_2 $.

$( make "surface" constant $)
$c surface $.

$( make surface variables $)
$v s_0 s_1 s_2 $.
$( make them "surface" $)
surface0 $f surface s_0 $.
surface1 $f surface s_1 $.
surface2 $f surface s_2 $.

$( Location is constant $)
$c Location $.
$( p_x Location r_0 is wff $)
wloc $a wff p_x Location r_0 $.

$( RegionOverlap is constant $)
$c RegionOverlap $.
$( r_1 RegionOverlap r_2 is wff $)
wregov $a wff r_1 RegionOverlap r_2 $. 

$( InRegion is a constant $)
$c InRegion $.
$( p_0 InRegion r_0 is wff $)
win $a wff p_0 InRegion r_0 $.

$( RegionContainment is constant $)
$c RegionContainment $.
$( r_1 RegionContainment r_2 is wff $)
wregcon $a wff r_1 RegionContainment r_2 $. 

$( AtomicRegion is constant $)
$c AtomicRegion $.
$( AtomicRegion r_0 is wff $)
wregatom $a wff AtomicRegion r_0 $.

$( RegionInterior is constant $)
$c RegionInterior $.
$( r_1 RegionInterior r_2 is wff $)
wregint $a wff r_1 RegionInterior r_2 $. 

$( RegionSurface is constant $)
$c RegionSurface $.
$( s_0 RegionSurface r_0 is wff $)
wregsur $a wff s_0 RegionSurface r_0 $. 

$( OnSurface is a constant $)
$c OnSurface $.
$( p_0 OnSurface s_0 is wff $)
won $a wff p_0 OnSurface s_0 $.

$( RegionFilm is constant $)
$c RegionFilm $.
$( s_0 RegionFilm r_0 is wff $)
wregf $a wff s_0 RegionFilm r_0 $. 

$( ExternallyConnected is constant $)
$c ExternallyConnected $.
$( r_1 ExternallyConnected r_2 is wff $)
wregec $a wff r_1 ExternallyConnected r_2 $. 

$( FilmConnected is constant $)
$c FilmConnected $.
$( r_1 FilmConnected r_2 is wff $)
wregfc $a wff r_1 FilmConnected r_2 $. 

$( Define locational functionality L. $)
df-lfu $a |- A. p_x A. r_1 A. r_2 ( ( p_x Location r_1 /\ p_x Location r_2 ) -> r_1 = r_2 ) $.

$( Define injectivity of location. $)
df-lin $a |- A. p_x A. p_y A. r_0 ( ( p_x Location r_0 /\ p_y Location r_0 ) -> p_x = p_y ) $.

$( Define region overlap O. $)
df-rov $a |- r_1 RegionOverlap r_2 <-> E. p_0 ( p_0 InRegion r_1 /\ p_0 InRegion r_2 ) $.

$( Define region containment C. $)
df-rco $a |- r_1 RegionContainment r_2 <-> A. p_0 ( p_0 InRegion r_2 -> p_0 InRegion r_1 ) $.

$( Define atomic region. $)
df-rat $a |- AtomicRegion r_0 <-> A. p_x A. r_1 ( 
  ( p_x Location r_1 /\ r_0 RegionContainment r_1 ) -> r_0 = r_1 $.

$( Atomic regions are disjoint. $)  
df-rdi $a |- A. r_1 A. r_2 ( ( AtomicRegion r_1 /\ AtomicRegion r_2 ) ->
  ( -. r_1 RegionOverlap r_2 \/ r_1 = r_2 ) ) $.
  
$( Atomic parts have atomic regions. $)
df-apar $a |- A. p_x A. r_0 ( ( p_x Location r_0 /\ Atom p_x ) -> AtomicRegion r_0 ) $.  
  
$( Parthood implies regional containment. This property is called expansivity. $)
$( Define expansivity. $)
df-pec $a |- A. p_x A. p_y A. r_1 A. r_2 ( 
  ( p_x Location r_1 /\ p_y Location r_2 /\ p_x PartOf p_y ) -> r_1 RegionContainment r_2 ) $.

$( Regions overlap only if one contains the other. This property is called
no interpenetration. $)
$( Define no interpenetration. $)
df-rni $a |- A. r_1 A. r_2 ( r_1 RegionOverlap r_2 -> 
  ( r_1 RegionContainment r_2 \/ r_2 RegionContainment r_1 ) ) $.

$( Define region interior RI. $)
df-ri $a |- r_1 RegionInterior r_2 <-> E. s_0 A. p_0 ( p_0 InRegion r_1 ->
  ( p_0 InRegion r_2 /\ -. p_0 OnSurface s_0 /\ s_0 RegionSurface r_2 ) ) $.

$( Define region surface RS. $)
df-rs $a |- s_0 RegionSurface r_0 <-> E. r_1 A. p_0 ( p_0 OnSurface s_0 ->
  ( p_0 InRegion r_0 /\ -. p_0 InRegion r_1 /\ r_1 RegionSurface r_0 ) ) $. 

$( Define region film RF. $)
df-rf $a |- s_0 RegionFilm r_0 <-> E. r_1 ( r_0 RegionInterior r_1 /\ s_0 RegionSurface r_1 ) $.

$( Define externally-connected regions EC. $)
df-exc $a |- r_1 ExternallyConnected r_2 <-> E. s_1 E. s_2 E. p_0
  ( ( s_1 RegionSurface r_1 /\ s_2 RegionSurface r_2 ) /\
    ( p_0 OnSurface s_1 /\ p_0 OnSurface s_2 ) ) $.

$( Define film-connected regions FC. $)
df-flmc $a |- r_1 FilmConnected r_2 <-> E. s_1 E. s_2 E. p_0
  ( ( s_1 RegionFilm r_1 /\ s_2 RegionFilm r_2 ) /\
    ( p_0 OnSurface s_1 /\ p_0 OnSurface s_2 ) ) $.

$( 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Time - Allen's Intervals
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$( exists is constant $)
$c exists $.
$( exists(A,t_0) is wff $)
wexists $a wff exists ( A , t_0 ) $. 

$( birth is constant $)
$c birth $.
$( birth(A) is a class (a time value, used via = and b~< throughout this
   section -- was wrongly typed wff before this fix; class syntax added so
   birth(A) actually parses against a real production instead of being
   accepted as unvalidated $a axiom text). $)
cbirth $a class birth ( A ) $.

$( death is constant $)
$c death $.
$( death(A) is a class, same reasoning as birth(A) above (was wrongly typed
   wff before this fix). $)
cdeath $a class death ( A ) $.

$( life is constant $)
$c life $.
$( life(A) is a class, same reasoning as birth(A) above (was wrongly typed
   wff before this fix). $)
clife $a class life ( A ) $.

$( precedes is constant $)
$c precedes $.
$( precedes(A,B) is wff $)
wprecedes $a wff precedes ( A , B ) $. 

$( meets is constant $)
$c meets $.
$( meets(A,B) is wff $)
wmeets $a wff meets ( A , B ) $. 

$( overlaps is constant $)
$c overlaps $.
$( overlaps(A,B) is wff $)
woverlaps $a wff overlaps ( A , B ) $. 

$( starts is constant $)
$c starts $.
$( starts(A,B) is wff $)
wstarts $a wff starts ( A , B ) $. 

$( during is constant $)
$c during $.
$( during(A,B) is wff $)
wduring $a wff during ( A , B ) $. 

$( finishes is constant $)
$c finishes $.
$( finishes(A,B) is wff $)
wfinishes $a wff finishes ( A , B ) $. 

$( coincident is constant $)
$c coincident $.
$( coincident(A,B) is wff $)
wcoincident $a wff coincident ( A , B ) $. 

$( nonoverlaps is constant $)
$c nonoverlaps $.
$( (nonoverlapsA,B) is wff $)
wnonoverlaps $a wff nonoverlaps ( A , B ) $. 


$( Define element existence predicate. $)
df-exists $a |- exists ( A , t_0 ) <-> -. boldI [[ A , t_0 ]] = (/) $.
 
$( Define birth time. Fixed 2026-08-26: the inner universal quantifier's body
   previously reused the outer t_0 instead of the bound t_1 (-. exists(A,t_0)
   instead of -. exists(A,t_1)), making the whole biconditional unsatisfiable
   for any t_0 > 0 (the reused-t_0 body directly contradicts the first
   conjunct exists(A,t_0)) -- a transcription slip already suspected in
   Lean4SFS/SFS.lean's own doc comment on birthIff but never back-ported to
   this axiom's actual text until now. $)
df-birth $a |- ( birth ( A ) = t_0 ) <->
  ( exists ( A , t_0 ) /\ A. t_1 e. ( 0 [,) t_0 ) -. exists ( A , t_1 ) ) $.

$( Define death time. Same transcription-slip fix as df-birth above. $)
df-death $a |- ( death ( A ) = t_0 ) <->
  ( exists ( A , t_0 ) /\ A. t_1 e. ( t_0 (,] now ) -. exists ( A , t_1 ) ) $.

$( Define lifetime. $)
df-lifetime $a |- life ( A ) = ( birth ( A ) [,] death ( A ) ) $.

$( Define Allen's interval precedes. $)
df-precedes $a |- precedes ( A , B ) <-> ( death ( A ) b~< birth ( B ) ) $.

$( Define Allen's interval meets. $)
df-meets $a |- meets ( A , B ) <-> ( death ( A ) = birth ( B ) ) $.

$( Define Allen's interval overlaps. $)
df-overlaps $a |- overlaps ( A , B ) <-> ( birth ( B ) b~< death ( A ) ) $.

$( Define Allen's interval starts. $)
df-starts $a |- starts ( A , B ) <-> 
  ( ( birth ( A ) = birth ( B ) ) /\ ( death ( B ) b~< death ( A ) ) ) $.

$( Define Allen's interval during. $)
df-during $a |- during ( A , B ) <-> 
  ( ( birth ( B ) b~<= birth ( A ) ) /\ ( death ( A ) b~<= death ( B ) ) ) $.

$( Define Allen's interval finishes. $)
df-finishes $a |- finishes ( A , B ) <-> 
  ( ( birth ( B ) b~< birth ( A ) ) /\ ( death ( A ) = death ( B ) ) ) $.

$( Define Allen's interval coincident. $)
df-coincident $a |- coincident ( A , B ) <-> 
  ( ( birth ( A ) = birth ( B ) ) /\ ( death ( A ) = death ( B ) ) ) $.

$( Define Allen's interval nonoverlaps. $)
df-nonoverlaps $a |- nonoverlaps ( A , B ) <->
  ( ( death ( A ) b~< birth ( B ) ) \/ ( death ( B ) b~< birth ( A ) ) ) $.

$( Variables for finitePartition and its consequences: finpn (the tick count),
   finbreaks (the tick sequence, a genuine setvar function), fini/finj (tick
   indices), findd (a generic Occurrence, ranged over universally). $)
$v finpn finbreaks fini finj findd $.
vfinpn $f setvar finpn $.
vfinbreaks $f setvar finbreaks $.
vfini $f setvar fini $.
vfinj $f setvar finj $.
vfindd $f setvar findd $.

$( finitePartition is a genuine new modeling commitment (2026-08-26, ported
   from Lean4SFS/SFS.lean's own finitePartition axiom, at direct request):
   every Occurrence's raw interpretation only ever changes at finitely many
   *shared* instants -- a single "event calendar," not a per-Occurrence one.
   Stated without reference to "pieces" to sidestep any half-open/closed
   boundary bookkeeping: if there is no shared tick strictly inside
   (t_1,t_2], d's value cannot have changed between t_1 and t_2.  This is
   what fixes next's permanent vacuity (bl.nextdense below) and changed's
   own gap -- not hyperreals, which cannot help here: two distinct time
   values are both standard reals, so neither "nothing between" nor
   "infinitesimally close" can ever hold for them, transfer principle or
   not (a dead end reached and rejected in Lean4SFS/SFS.lean before this
   axiom was proposed there). $)
finitePartition $a |- E. finpn e. NN0 E. finbreaks
  ( ( ( finbreaks : ( 0 ... finpn ) --> TIME /\
        ( ( finbreaks ` 0 ) = 0 /\ ( finbreaks ` finpn ) = now ) ) /\
      A. fini e. ( 0 ... finpn ) A. finj e. ( 0 ... finpn )
        ( fini < finj -> ( finbreaks ` fini ) b~< ( finbreaks ` finj ) ) ) /\
    A. findd A. t_1 A. t_2 ( t_1 b~<= t_2 ->
      ( -. E. fini e. ( 0 ... finpn ) ( finbreaks ` fini ) e. ( t_1 (,] t_2 ) ->
        boldI [[ findd , t_1 ]] = boldI [[ findd , t_2 ]] ) ) ) $.

$( isTick is constant $)
$c isTick $.
$( isTick(t_1) is wff: t_1 is one of the finitely many shared ticks --
   existentially quantifying its own witnessing finitePartition instance,
   rather than extracting one canonical global choice the way
   Lean4SFS/SFS.lean's tickCount/ticks do (Metamath's iota/`the x such
   that' operator needs *unique* existence to be usable, and
   finitePartition's own witness is not unique -- any finite refinement of
   a valid partition is itself valid). $)
wistick $a wff isTick ( t_1 ) $.

$( Define isTick: t_1 equals some tick of some valid finite partition. $)
df-istick $a |- ( isTick ( t_1 ) <->
  E. finpn e. NN0 E. finbreaks
    ( ( ( ( finbreaks : ( 0 ... finpn ) --> TIME /\
            ( ( finbreaks ` 0 ) = 0 /\ ( finbreaks ` finpn ) = now ) ) /\
          A. fini e. ( 0 ... finpn ) A. finj e. ( 0 ... finpn )
            ( fini < finj -> ( finbreaks ` fini ) b~< ( finbreaks ` finj ) ) ) /\
        A. findd A. t_2 A. t_3 ( t_2 b~<= t_3 ->
          ( -. E. fini e. ( 0 ... finpn ) ( finbreaks ` fini ) e. ( t_2 (,] t_3 ) ->
            boldI [[ findd , t_2 ]] = boldI [[ findd , t_3 ]] ) ) ) /\
      E. fini e. ( 0 ... finpn ) ( finbreaks ` fini ) = t_1 ) $.

$( next is constant $)
$c next $.
$( next(t_1,t_2) is wff $)
wnext $a wff next ( t_1 , t_2 ) $.

$( Define next: t_2 immediately follows t_1.  Redefined 2026-08-26 (ported
   from Lean4SFS/SFS.lean's own redesign, at direct request; was "t_1 b~<
   t_2 and no instant strictly between," provably vacuous on dense TIME
   regardless of t_1/t_2 -- see the retired bl.nextdense) as "t_1, t_2 are
   both shared ticks (isTick), t_1 b~< t_2, and no *other tick* lies
   strictly between them" -- genuine successor-in-a-finite-set, not "no
   real number between," so no longer forced to be false for every input.
   The witness for "no OTHER tick between" is a genuine setvar x, bridged
   to class position via cv, same reasoning as the original df-next. $)
df-next $a |- ( next ( t_1 , t_2 ) <->
  ( ( ( isTick ( t_1 ) /\ isTick ( t_2 ) ) /\ t_1 b~< t_2 ) /\
    -. E. x ( ( isTick ( x ) /\ t_1 b~< x ) /\ x b~< t_2 ) ) ) $.

$( next(t_1,t_2) implies t_1 precedes t_2.  Repaired 2026-08-26 for df-next's
   own redesign (isTick(t_1)/\isTick(t_2)/\t_1 b~< t_2, the third conjunct
   of a left-associated 4-way /\, was the whole 2nd conjunct before). $)
bl.nexttp $p |- ( next ( t_1 , t_2 ) -> t_1 b~< t_2 ) $=
  vt1 vt2 wnext
  vt1 wistick vt2 wistick wa
  vt1 vt2 wtp
  vt1 vt2 wnext
  vt1 wistick vt2 wistick wa vt1 vt2 wtp wa
  vx cv wistick vt1 vx cv wtp wa vx cv vt2 wtp wa vx wex wn
  vx vt1 vt2
  df-next simplbi
  simprd $.

$( t_2 is a set given the (t_1 b~<t_2 /\ t_2 b~<t_3) witness data; helper for
   bl.nextwit. $)
bl.nextev $p |- ( ( t_2 e. TIME /\ ( t_1 b~< t_2 /\ t_2 b~< t_3 ) ) ->
  t_2 e. _V ) $=
  vt2 ctime wcel vt1 vt2 wtp vt2 vt3 wtp wa wa vt2 ctime wcel vt2 cvv wcel vt2
  ctime wcel vt1 vt2 wtp vt2 vt3 wtp wa simpl vt2 ctime elex syl $.

$( Existential witnessing for the "no instant between" clause of df-next: if
   t_2 sits strictly between t_1 and t_3 (via b~<), then some x does.  This is
   the lemma that needed bl.tpeq1/bl.tpeq2 above -- b~< is not wbr-based, so
   the standard sbcbr1g/sbcbr2g machinery does not apply to it; sbcieg
   (driven by the congruence axioms) is used instead. $)
$d x t_1 t_2 t_3 $.
bl.nextwit $p |- ( ( t_2 e. TIME /\ ( t_1 b~< t_2 /\ t_2 b~< t_3 ) ) ->
  E. x ( t_1 b~< x /\ x b~< t_3 ) ) $=
  vt2 ctime wcel vt1 vt2 wtp vt2 vt3 wtp wa wa vt1 vx cv wtp vx cv vt3 wtp wa
  vx vt2 wsbc vt1 vx cv wtp vx cv vt3 wtp wa vx wex vt2 ctime wcel vt1 vt2 wtp
  vt2 vt3 wtp wa wa vt1 vx cv wtp vx cv vt3 wtp wa vx vt2 wsbc vt1 vt2 wtp vt2
  vt3 wtp wa vt2 ctime wcel vt1 vt2 wtp vt2 vt3 wtp wa simpr vt2 ctime wcel vt1
  vt2 wtp vt2 vt3 wtp wa wa vt2 cvv wcel vt1 vx cv wtp vx cv vt3 wtp wa vx vt2
  wsbc vt1 vt2 wtp vt2 vt3 wtp wa wb vt1 vt2 vt3 bl.nextev vt1 vx cv wtp vx cv
  vt3 wtp wa vt1 vt2 wtp vt2 vt3 wtp wa vx vt2 cvv vx cv vt2 wceq vt1 vx cv wtp
  vt1 vt2 wtp vx cv vt3 wtp vt2 vt3 wtp vx cv vt2 vt1 bl.tpeq2 vx cv vt2 vt3
  bl.tpeq1 anbi12d sbcieg syl mpbird vt1 vx cv wtp vx cv vt3 wtp wa vx vt2
  spesbc syl $.

$( Uniqueness of next (eq:bl.nextuniq in Supplemental-Semantics, matching
   Lean4SFS/SFS.lean's own next_uniq, 2026-08-26).  Genuinely reinstated
   (was vacuously true before df-next's redesign, since next was
   unsatisfiable for every input).  Statement includes explicit
   t_2/t_3 e. TIME hypotheses (df-next's own isTick clauses don't by
   themselves give TIME-membership without a further "isTick(t) -> t e.
   TIME" helper lemma, not yet added) -- a real, well-formed theorem,
   correctly typed and citable, but NOT YET PROVED: the natural proof
   (real-number trichotomy on t_2,t_3 via lttri3, bridged from b~< via
   df-bl.before, deriving a contradiction in each non-equal case by
   instantiating the *other* next's "no tick between" clause at the
   would-be-between value) needs a genuinely new existential-witnessing
   helper mirroring bl.nextwit above but carrying an extra isTick(x)
   conjunct through the same sbcieg-driven substitution machinery --
   bl.nextwit itself doesn't suffice, its own witness lacks isTick(x).
   Left here as a known, explicitly-scoped gap (2026-08-26 investigation
   found this exceeds "bounded effort," matching the file's existing
   unproved-placeholder convention: bl.ty, bl.tyt, bl.atintroc, povrfl,
   punrfl, pimrfl, pdjrfl) rather than guessed at or rushed. $)
bl.nextuniq $p |- ( ( ( t_2 e. TIME /\ t_3 e. TIME ) /\
  ( next ( t_1 , t_2 ) /\ next ( t_1 , t_3 ) ) ) -> t_2 = t_3 ) $= ? $.

$( openLeft is constant $)
$c openLeft $.
$( openLeft(A) is wff $)
wopenleft $a wff openLeft ( A ) $.

$( openRight is constant $)
$c openRight $.
$( openRight(A) is wff $)
wopenright $a wff openRight ( A ) $.

$( nearlymeets is constant $)
$c nearlymeets $.
$( nearlymeets(A,B) is wff $)
wnearlymeets $a wff nearlymeets ( A , B ) $.

$( Define the Allen's-interval-adjacent relation nearlymeets (Allen.kerml's own
   nearlyMeets, df-nearlymeets in Supplemental-Semantics): A and B don't meet,
   but there is no instant strictly between death(A) and birth(B) -- either
   because they share that boundary instant and A is open-right or B is
   open-left there, or because there simply is no instant between under
   next(), even without either boundary being open. $)
df-nearlymeets $a |- ( nearlymeets ( A , B ) <->
  ( ( ( birth ( B ) = death ( A ) ) /\ ( openRight ( A ) \/ openLeft ( B ) ) )
    \/ next ( death ( A ) , birth ( B ) ) ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  KerML Element Representation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Kind of Element $)

$c kind $.
$c Element $.
$c Relationship $.
$c Dependency $.
$( $c Type $. $)
$c Feature $.
$c Classifier $.
$c DataType $.
$c Class $.
$c Structure $.
$c Association $.
$c Connector $.
$c Behavior $.
$c Function $.
$c Expression $.
$c Interaction $.

$( Define element kind. $)
df-kind $a |- kind = { Element , Relationship , Dependency , Feature , Classifier ,
  DataType , Class , Structure , Association , Connector , Behavior , Function ,
  Expression , Interaction } $.

$( Unique Identifier creation from a Class Identifier by appending a wonce $)

$( Class of Class Identifiers: strings that are either a simple identifier, or a
   qualified name -- a sequence of identifiers separated by "::". $)
$c CI $.
cci $a class CI $.

$( Class of Unique Identifiers: the class of all allocated unique identifiers. $)
$c UI $.
cuid $a class UI $.

$( The tag-boundary separator string ("\#") inserted between a class identifier and a
   wonce when forming a unique identifier. $)
$c tb $.
ctagb $a class tb $.

$( Class of "wonces" (word-once identifiers): the countably-infinite sequence
   a, b, ..., z, aa, ab, ..., az, ba, ... used to make unique identifiers distinct. $)
$c wonce $.
cwonce $a class wonce $.

$( mkUid, as a class-valued function from Class Identifiers to Unique Identifiers. $)
$c mkUid $.
cmkuid $a class mkUid $.

$( Define creation of a Unique Identifier ` ( mkUid ` A ) ` from a Class Identifier
   ` A ` by appending the tag-boundary and a wonce. $)
df-wonce $a |- ( mkUid ` A ) = ( ( A ++ tb ) ++ wonce ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  KerML Type Definition
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Class of identifiers: strings naming KerML elements. Already declared, unused
   until now, at the top of this file. $)
cID $a class ID $.

$( The kind-marker for a bare ` type x ` declaration: an element whose kind is
   neither a Classifier nor a Feature (KerML 8.4.3.2). Deliberately NOT one of
   df-kind's 14 enumerated tags: the book treats V_C u. V_F as a proper subset
   of V_T, so Type marks a design element outside that enumeration, not a
   15th member of it. Token already declared, unused until now, at the top of
   this file. $)
cType $a class Type $.

$( The design: the set of all elements in the database or workspace (KerML
   Core Semantics 2.1.2). Represented as a set of df-rep triples
   ` <. k , id , C >. ` -- left a fresh primitive class, its internal
   structure not otherwise constrained here. $)
$c Design $.
cDesign $a class Design $.

$( Semantics of KerML text ` type A `: A is an identifier (a String), and
   ` <. Type , A , C >. e. Design ` is the formal reading of that concrete
   declaration itself -- some design element's df-rep triple has kind Type
   and id A -- rather than an unstructured stand-in predicate. Given that
   premise, C (the type's extent, i.e. what A denotes) is a genuine set. $)
${
  df-type.1 $e |- A e. ID $.
  df-type.2 $e |- <. Type , A , C >. e. Design $.
  df-type $a |- C e. _V $.
$}

$( V_T: the set of all Types in the design (KerML Core Semantics 2.1.1's vocabulary
   triple V = <. V_T , V_C , V_F >.), a pre-existing primitive df-types constrains
   rather than fully defines (matching the book's own implication, not equation,
   form). $)
$c VT $.
cVT $a class VT $.

$( Semantics of KerML text ` type x `, restated as membership in V_T: for every
   identifier x, if x is declared with the bare type keyword (the same
   Design-triple-membership reading df-type gives that text), then x e. V_T. Uses
   the same genuine text-to-Design-triple association as df-type, not a separate
   stand-in predicate. $)
df-types $a |- ( x e. ID -> ( E. y <. Type , x , y >. e. Design -> x e. VT ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Variable Feature Access
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( occ, feat, inst, valu, boo, flag are new class variables for the KerML
   Domain library's variable-feature-accessing functions/behaviors below
   (Chapter/KernelSemanticsChapter.tex sec 3.1.4), mirroring Domain.kerml's own
   d/f/tau/v/e/b parameter names. $)
$v occ feat inst valu boo flag $.
vocc  $f class occ $.
vfeat $f class feat $.
vinst $f class inst $.
vvalu $f class valu $.
vboo  $f class boo $.
vflag $f class flag $.

$( tv is a new setvar variable, the bound variable for the restricted
   quantifications below -- must be setvar, not class, matching how
   bl.nextwit above needed a genuine setvar witness x rather than reusing
   the class-typed t_1/t_2/t_3. $)
$v tv $.
vtv $f setvar tv $.

$( FeatAcc is constant $)
$c FeatAcc $.
$( FeatAcc(occ,feat), value-reading feature access ("occ::feat" in KerML), is
   class. $)
cfeatacc $a class FeatAcc ( occ , feat ) $.

$( FeatAccP is constant $)
$c FeatAccP $.
$( FeatAccP(occ,boo,inst), predicate-reading feature access for a Boolean-valued
   feature at a given instant, is wff. A genuinely independent primitive from
   FeatAcc, not derived from it -- there is no sound way to recover "this
   feature value denotes true" from FeatAcc's class-valued result alone. $)
wfeataccp $a wff FeatAccP ( occ , boo , inst ) $.

$( TrueItem, FalseItem are constants: opaque canonical values standing for the
   Boolean literals true/false, needed once GetChangeToTrue/GetChangeToFalse
   compare their output against a literal. $)
$c TrueItem FalseItem $.
ctrueitem  $a class TrueItem  $.
cfalseitem $a class FalseItem $.

$( Get is constant $)
$c Get $.
$( Get(occ,feat,inst) is class $)
cget $a class Get ( occ , feat , inst ) $.

$( Define Get: the value of occ's feature feat at inst is the interpretation of
   occ::feat at inst. $)
df-Get $a |- Get ( occ , feat , inst ) = boldI [[ FeatAcc ( occ , feat ) , inst ]] $.

$( GetNow is constant $)
$c GetNow $.
$( GetNow(occ,feat) is class $)
cgetnow $a class GetNow ( occ , feat ) $.

$( Define GetNow: a convenience specialization of Get, always read at now. $)
df-GetNow $a |- GetNow ( occ , feat ) = Get ( occ , feat , now ) $.

$( SetNow is constant $)
$c SetNow $.
$( SetNow(occ,feat,valu) is wff $)
wsetnow $a wff SetNow ( occ , feat , valu ) $.

$( Define SetNow: the write counterpart to Get/GetNow, constraining occ's
   feature feat to equal valu at now. $)
df-SetNow $a |- ( SetNow ( occ , feat , valu ) <->
  Get ( occ , feat , now ) = valu ) $.

$( GetChange is constant $)
$c GetChange $.
$( GetChange(occ,feat,inst,valu) is wff $)
wgetchange $a wff GetChange ( occ , feat , inst , valu ) $.

$( Define GetChange: if occ's feature feat was stable at Get(occ,feat,inst)
   throughout [inst,now) and has changed as of now, then valu is that new
   (changed) value. $)
df-GetChange $a |- ( GetChange ( occ , feat , inst , valu ) <->
  ( ( -. Get ( occ , feat , inst ) = Get ( occ , feat , now ) /\
      A. tv e. ( inst [,) now ) Get ( occ , feat , tv ) = Get ( occ , feat , inst ) )
    -> valu = Get ( occ , feat , now ) ) ) $.

$( GetBooleanChange is constant $)
$c GetBooleanChange $.
$( GetBooleanChange(occ,boo,inst,flag) is wff $)
wgetbooleanchange $a wff GetBooleanChange ( occ , boo , inst , flag ) $.

$( Define GetBooleanChange: GetChange specialized to a Boolean-valued feature,
   restated verbatim with boo/flag in place of feat/valu. $)
df-GetBooleanChange $a |- ( GetBooleanChange ( occ , boo , inst , flag ) <->
  GetChange ( occ , boo , inst , flag ) ) $.

$( GetChangeToTrue is constant $)
$c GetChangeToTrue $.
$( GetChangeToTrue(occ,boo,inst,flag) is wff $)
wgetchangetotrue $a wff GetChangeToTrue ( occ , boo , inst , flag ) $.

$( Define GetChangeToTrue: does not wait if occ's feature boo is already true
   -- if boo holds at now and did not hold throughout [inst,now), flag is
   immediately true. Uses FeatAccP (the predicate reading), not Get. $)
df-GetChangeToTrue $a |- ( GetChangeToTrue ( occ , boo , inst , flag ) <->
  ( ( FeatAccP ( occ , boo , now ) /\
      A. tv e. ( inst [,) now ) -. FeatAccP ( occ , boo , tv ) )
    -> flag = TrueItem ) ) $.

$( GetChangeToFalse is constant $)
$c GetChangeToFalse $.
$( GetChangeToFalse(occ,boo,inst,flag) is wff $)
wgetchangetofalse $a wff GetChangeToFalse ( occ , boo , inst , flag ) $.

$( Define GetChangeToFalse: mirror image of GetChangeToTrue. $)
df-GetChangeToFalse $a |- ( GetChangeToFalse ( occ , boo , inst , flag ) <->
  ( ( -. FeatAccP ( occ , boo , now ) /\
      A. tv e. ( inst [,) now ) FeatAccP ( occ , boo , tv ) )
    -> flag = FalseItem ) ) $.

$( changed is constant $)
$c changed $.
$( changed(occ,t_1) is class: the time when occ's interpretation most recently
   changed before t_1 (Chapter/KernelSemanticsChapter.tex sec 3.1.5). $)
cchanged $a class changed ( occ , t_1 ) $.

$( Redefined 2026-08-26 (ported from Lean4SFS/SFS.lean's own changed redesign,
   at direct request): the original characterizing biconditional above was
   close to vacuous for ordinary step-function occ -- for occ constant A
   before some transition and B from it on, and any t_1 that isn't itself a
   fresh transition instant, *no* t_2 satisfied its three conditions jointly
   (the exact transition point failed the "differs" disjunct, its value
   already matching occ's value at t_1; every earlier t_2 failed the
   open-interval constancy clause, since (t_2,t_1) straddles the
   transition).  Grounded in isTick/finitePartition instead: changed(occ,t_1)
   is t_2 exactly when t_2 is a shared tick at or before t_1, occ's value
   matches its own value at t_1 throughout every tick from t_2 up to t_1
   (inclusive), and either t_2=0 (occ hasn't changed before t_1 at all) or
   the tick immediately before t_2 has a *different* value from t_1's --
   i.e. t_2 is genuinely the start of t_1's own current, matching-value run,
   not merely some earlier point that happens to agree.  Total and
   satisfiable for every occ/t_1, not merely characterized (finiteness of
   the tick set is what makes this well-posed -- a full explicit Finset.max'-
   style *construction* of changed as an unconditional class term, matching
   Lean4SFS/SFS.lean's own noncomputable def exactly, would need its own new
   canonical-choice/uniqueness apparatus beyond what isTick's per-formula
   existential provides; not attempted here, this is the characterizing-axiom
   level port only, same epistemic status the original df-bl.changed already
   had). $)
$v tw $.
vtw $f class tw $.
df-bl.changed $a |- ( changed ( occ , t_1 ) = t_2 <->
  ( ( ( isTick ( t_2 ) /\ t_2 b~<= t_1 ) /\
      A. tv ( ( isTick ( tv ) /\ ( t_2 b~<= tv /\ tv b~<= t_1 ) ) ->
        boldI [[ occ , tv ]] = boldI [[ occ , t_1 ]] ) ) /\
    ( t_2 = 0 \/
      E. tw ( next ( tw , t_2 ) /\ -. boldI [[ occ , tw ]] = boldI [[ occ , t_1 ]] ) ) ) ) $.

$( timeof is constant $)
$c timeof $.
$( timeof(ph) is class: the first instant at which predicate ph holds
   (Chapter/KernelSemanticsChapter.tex sec 3.1.6). $)
ctimeof $a class timeof ( ph ) $.

$( Define timeof: timeof(ph) = t_1 iff ph holds at t_1 and ph does not hold at
   any instant strictly before t_1. $)
df-bl.timeof $a |- ( timeof ( ph ) = t_1 <->
  ( boldI [[ ph , t_1 ]] /\
    A. tv e. ( 0 [,) t_1 ) -. boldI [[ ph , tv ]] ) ) $.

$( ******************* End of Supplemental Formal Semantics ******************* $)
