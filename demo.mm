$( constants $)
	$c 0 + = -> ( ) term wff |- $.
$( metavariables $)
	$v t r s P Q $.
$( metavariable properties $)
	tt $f term t $.
	tr $f term r $.
	ts $f term s $.
	wp $f wff P $.
	wq $f wff Q $.
$( properties of term and wff $)
	tze $a term 0 $.
	tpl $a term ( t + r ) $.
	weq $a wff t = r $.
$( axioms $)
	a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
	a2 $a |- ( t + 0 ) = t $.
$( modus ponens $)
	${
		min $e |- P $.
		maj $e |- ( P -> Q ) $.
		mp  $a |- Q $.
	$}
	wim $a wff ( P -> Q ) $.

$( th1 $)
	th1 $p |- t = t $=
	tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
	tt weq tt tze tpl tt weq tt tt weq wim tt a2
	tt tze tpl tt tt a1 mp mp
	$.

$( th2 $)
	th2 $p |- r = r $=
	tr th1 $.

$( th3 $)
	${
		$v u $.
		tu $f term u $.
		th3 $p |- u = u $=
		tu th2 $.
	$}

$( th4 $)
	th4 $p |- s = s $=
	ts th3 $.
