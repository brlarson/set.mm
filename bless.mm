$( bless.mm $)

$( These theorems are verified by MM>verify proof *
  but can't be parsed by mmj2, so they can't be used automatically $)


  
$( read in set.mm$)
$[ /Users/brianlarson/git3/set.mm/set.mm $]  


$( Make any wff first in conjunction wff-list $)
bl.ancomphfirst $p |- ( /\( l_ ph l2 )x <-> /\( ph l2 l_ )x )
	$= wl1 wph wfl1 wl2 wfl2 bl.ancomwlwl $.
  $( [brl] $) $( [24-Mar-2011] $)

$( Make any wff last in conjunction wff-list $)
bl.ancomphlast $p |- ( /\( l_ ph l2 )x <-> /\( l2 l_ ph )x )
	$= wl1 wph wfl1 wfl2 wl2 bl.ancomwlwl $.
  $( [brl] $) $( [24-Mar-2011] $)

$( Pull middle wff from conjunction wff-list $)
bl.anpmw $p |- ( /\( l_ ph l2 )x <-> ( ph /\ /\( l2 l_ )x ) )
	$= wl1 wph wfl1 wfl2 wl2 wfl2 wland wph wfl1 wl2 wfl2 wl1 wfl2 wland wph wl2 wl1
  wfl2 wland wa wph wl1 wl2 bl.ancomphfirst wph wl2 wl1 wfl2 bl.anpfw bitri $.
  $( [brl] $) $( [24-Mar-2011] $)

$( Absorb parentheses, middle term in conjunction wff-list $)
bl.anabpm $p |- ( /\( l_ /\( l2 )x l3 )x <-> /\( l_ l2 l3 )x )
	$= 
  wl1 wl2 wland wfl1 wl3 wfl2 wfl2 wland wl2 wland wfl1 wl3 wl1 wfl2 wfl2 wland wl2 wl3
  wl1 wfl2 wfl2 wland wl1 wl2 wl3 wfl2 wfl2 wland wl1 wl2 wland wfl1 wl3 wfl2
  bl.ancomwlwl wl2 wl3 wl1 wfl2 bl.anabpf wl2 wl3 wfl2 wl1 bl.ancomwlwl 3bitri
  $.
  $( [brl] $) $( [24-Mar-2011] $)


$( Make any wff first in disjunction wff-list $)
bl.orcomphfirst $p |- ( \/( l_ ph l2 )x <-> \/( ph l2 l_ )x )
	$= wl1 wph wfl1 wl2 wfl2 bl.orcom $.
  $( [brl] $) $( [24-Mar-2011] $)

$( Make any wff last in disjunction wff-list $)
bl.orcomphlast $p |- ( \/( l_ ph l2 )x <-> \/( l2 l_ ph )x )
	$= wl1 wph wfl1 wfl2 wl2 bl.orcom $.
  $( [brl] $) $( [24-Mar-2011] $)


$( Pull middle wff from disjunction wff-list $)
bl.orpmw $p |- ( \/( l_ ph l2 )x <-> ( ph \/ \/( l2 l_ )x ) )
	$= wl1 wph wfl1 wfl2 wl2 wfl2 wlo wph wfl1 wl2 wfl2 wl1 wfl2 wlo wph wl2 wl1
  wfl2 wlo wo wph wl1 wl2 bl.orcomphfirst wph wl2 wl1 wfl2 bl.orpfw bitri $.
  $( [brl] $) $( [24-Mar-2011] $)


$( Absorb parentheses, middle term in disjunction wff-list $)
bl.orabpm $p |- ( \/( l_ \/( l2 )x l3 )x <-> \/( l_ l2 l3 )x )
	$= 
  wl1 wl2 wlo wfl1 wl3 wfl2 wfl2 wlo wl2 wlo wfl1 wl3 wl1 wfl2 wfl2 wlo wl2 wl3
  wl1 wfl2 wfl2 wlo wl1 wl2 wl3 wfl2 wfl2 wlo wl1 wl2 wlo wfl1 wl3 wfl2
  bl.orcom wl2 wl3 wl1 wfl2 bl.orabpf wl2 wl3 wfl2 wl1 bl.orcom 3bitri
	$.
  $( [brl] $) $( [24-Mar-2011] $)

$(  And-Introduction Schema of wff $)
bl.ais $p |- ( /\( l_ ph l2 )x -> ph )
$(  used by AXIOM.and_intoduction_schema $)
$(  to set Reason.AND_INTRO $)
$(  "And Introduction Schema (aisph):  (X and Y)->X" $)
	$= wl1 wph wfl1 wfl2 wl2 wfl2 wland wph wl2 wl1 wfl2 wland wa wph wph wl1 wl2
  bl.anpmw wph wl2 wl1 wfl2 wland simpl sylbi $.
  $( [brl] $) $( [24-Mar-2011] $)


$(  And-Introduction Schema of wff-list $)
bl.aiswl $p |- ( /\( l_ l2 l3 )x -> /\( l2 )x )
$(  used by AXIOM.multiterm_and_intoduction_schema  $)
$(  to set Reason.AND_INTRO_MULTIPLE $)
$(  "And Introduction Schema (aiswl):  (X and Y and Z) -> (X and Y)" $)
	$= wl1 wl2 wfl2 wl3 wfl2 wland wl2 wland wl3 wl1 wfl2 wland wa wl2 wland wl1 wl2
  wfl2 wl3 wfl2 wland wl1 wl2 wland wfl1 wfl2 wl3 wfl2 wland wl2 wland wl3 wl1
  wfl2 wland wa wl1 wl2 wl3 bl.anabpm wl2 wland wl1 wl3 bl.anpmw bitr3i wl2
  wland wl3 wl1 wfl2 wland simpl sylbi $.
  $( [brl] $) $( [24-Mar-2011] $)






