| package |
package := Package name: 'mj348711'.
package paxVersion: 1;
	basicComment: 'Michal Jaron
nr. 348711

Jezyki i paradygamty programowania, zadanie 4 - small talk.'.

package basicScriptAt: #postinstall put: 'Smalltalk at: #L put: (C % nil).
V reset.'.

package classNames
	add: #C;
	add: #Conjunction;
	add: #Database;
	add: #Fitter;
	add: #Matcher;
	add: #Pair;
	add: #Prolog;
	add: #Rule;
	add: #Term;
	add: #V;
	yourself.

package binaryGlobalNames: (Set new
	yourself).

package globalAliases: (Set new
	yourself).

package setPrerequisites: (IdentitySet new
	add: '..\Core\Object Arts\Dolphin\Base\Dolphin';
	yourself).

package!

"Class Definitions"!

Object subclass: #Conjunction
	instanceVariableNames: 'terms'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Object subclass: #Database
	instanceVariableNames: 'facts rules'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Object subclass: #Fitter
	instanceVariableNames: 'dbIndex database rule pos matchers moje chg raw'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Object subclass: #Matcher
	instanceVariableNames: 'container'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Object subclass: #Prolog
	instanceVariableNames: 'database'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Object subclass: #Rule
	instanceVariableNames: 'head body vars'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Object subclass: #Term
	instanceVariableNames: 'type value'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Term subclass: #C
	instanceVariableNames: ''
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Term subclass: #Pair
	instanceVariableNames: 'car cdr'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Term subclass: #V
	instanceVariableNames: 'addr refers'
	classVariableNames: 'Index UsedVars VarsDict'
	poolDictionaries: ''
	classInstanceVariableNames: ''!

"Global Aliases"!


"Loose Methods"!

"End of package definition"!

"Source Globals"!

"Classes"!

Conjunction guid: (GUID fromString: '{8DA2ACFB-7179-49CF-8981-E69A5070108F}')!
Conjunction comment: 'List of terms ( t1 & t2...) == logical and.'!
!Conjunction categoriesForClass!Kernel-Objects! !
!Conjunction methodsFor!

& t
	(t isMemberOf: Conjunction) ifTrue: [terms := terms, t terms. ^self].
	self add: t.
	^ self!

add: t
	| len |
	len := terms size.
	terms resize: (len + 1).
	terms at: (len +1) put: t!

init
	terms := Array new.!

terms
	^terms! !
!Conjunction categoriesFor: #&!public! !
!Conjunction categoriesFor: #add:!public! !
!Conjunction categoriesFor: #init!public! !
!Conjunction categoriesFor: #terms!public! !

!Conjunction class methodsFor!

new
	| tmp |
	tmp := super new.
	tmp init.
	^ tmp.! !
!Conjunction class categoriesFor: #new!public! !

Database guid: (GUID fromString: '{4443FA00-4D98-4D9B-8059-C971BC97C6FD}')!
Database comment: 'Every object represents all konwledge database. It stores fact and rules in the same way. Facty in stored as rule with empty body.
In addition to storing rules it allows to find unfication with any rules(look at find:index:). As in prolog rules as stored in indexed way.'!
!Database categoriesForClass!Kernel-Objects! !
!Database methodsFor!

addFact: fact
	| tmp |
	tmp := Pair new.
	tmp car: fact cdr: [].
	self addRule: tmp " Just rule with empty body"!

addRule: rule
	| len tmp |
	len := rules size.
	rules resize: (len + 1).
	len := len + 1.
	tmp := Rule new.
	tmp head: (rule car) body: (rule cdr).
	rules at: len put: tmp!

find: term index: index
	" Try to find unfication wirh some of rules from database, starting matching from index"
	| len  work i t h p|
	p := Pair new.
	i := index.
	len := rules size.
	work := true.
	[(i <= len) & (work)] whileTrue: " Iterate to find match or to prove that that is not matching rule"
			[
			  t := (rules at: i) trans.
			  h := t car head. 
			  " Is there unfication of destination term and particular term from db?"
			  term go: h do: [work := false. p car: (t car body) cdr: i . ^p].
			  "V delete: t cdr."
			  i := i + 1.
			].
	^Error "no match"
	


!

init
	facts := Array new.
	rules := Array new! !
!Database categoriesFor: #addFact:!public! !
!Database categoriesFor: #addRule:!public! !
!Database categoriesFor: #find:index:!public! !
!Database categoriesFor: #init!public! !

!Database class methodsFor!

new
	| tmp |
	tmp := super new.
	tmp init.
	^ tmp! !
!Database class categoriesFor: #new!public! !

Fitter guid: (GUID fromString: '{279709FA-986A-43DB-BE4C-8F22E0CFA193}')!
Fitter comment: 'It reprents node in tree of prolog searching(encapsulate backtracking etc.).

It takes rule(probabaly partially matched) and tries to to satisfie goal, based on konwledge from database. It allows backtracking and multiple solution looking by remebering dbIndex(index of last matched rule from db) an by rembering position (pos) it list of goals to satisfy.

match and match: block (the same for loops) are a little bit different becasue of some rule/conds are just leafs in seraching tree and if satisfy they can execute block.

chg variable is list of vairables that was changed by matcher (unified with some value). That is used for recovering and backtracking.'!
!Fitter categoriesForClass!Kernel-Objects! !
!Fitter methodsFor!

createMatchers: fit
	| tmp |
	raw := fit.
	matchers := Array new.
	(fit size > 0) ifTrue: [fit do: [:elem | tmp:= Fitter new. tmp  setRule: (elem eval) setDatabase: database. matchers resize: ((matchers size) + 1). matchers  at: (matchers size) put: tmp ]].!

dbFind
	" Try to find next rule that matches with your rule"
	| res maj|
	maj := rule eval .
	res := database find: maj index: dbIndex.
	(res == Error) ifTrue: [^false].
	dbIndex := res cdr + 1. " Next time look for rules under found"
	^res car.!

loop
	| ans ret |
	" Try to unify all goals"
	( matchers == nil) ifTrue: [chg do: [ :x | x  zeros]. chg := Array new. ret := false. pos:=1.].
	(ret == false) ifTrue: [^ret].
	[ (pos>= 1) & (pos <= (matchers size))] whileTrue: 
		[
		  ans := (matchers at: pos) match.
		 (ans == true) 	ifTrue: 	[
								pos :=pos + 1. (pos <= (matchers size)) ifTrue: [ (matchers at: pos) setRule: ( (raw at: pos) eval) setDatabase: database ] " Next rule to satisfy"
							]
					ifFalse:	[pos:= pos - 1] 
		].
	(pos < 1) ifTrue: [ret := false] ifFalse: [ret :=true. pos:= (matchers  size)]. ^ret " All rules are correct. Success!!"!

loop: block
	| ans ret|
	( matchers == nil) ifTrue: [chg do: [ :x | x  zeros]. chg := Array new. ret := false. pos:=1.].
	(ret == false) ifTrue: [^ret].
	[(pos>= 1) & (pos <= (matchers size))] whileTrue: 
		[
		  (pos == (matchers size)) 	ifTrue: [ ans := (matchers at: pos)  match: block.  (ans == false) ifTrue: [pos :=pos - 1] ifFalse: []] "ifFalse: it allows backtracking, if matcher returns true than try the same matcher"
							ifFalse:  [
										ans := (matchers at: pos)  match. (ans == false) 
										ifTrue: [pos:=pos- 1]
										ifFalse:  [pos :=pos + 1. (pos <= (matchers size)) ifTrue: [ (matchers at: pos) setRule: ( (raw at: pos)  eval) setDatabase: database ] ] 
									].
		].
	(pos < 1) ifTrue: [ret:=false] ifFalse: [ pos:=(matchers size). ret:=true]. ^ret.!

match
	| ans dbFound  tmp ret|
	"  Visible for world method for insisting satisfing goal"
	ret:=false.
	dbFound := true.
	[(dbFound == false) not] whileTrue: 
	[	
		ans := self loop. 
		(ans == false) 	ifTrue: [	
							tmp:= rule eval getVarsList. 
							dbFound := self dbFind. "look for rule to match"
							(dbFound == false) ifTrue: [pos:=1. ret:=false. ^false]. 
							chg:= tmp difference: (rule eval getVarsList ). " which vars was chagned by you"
							self createMatchers: dbFound.
							pos:=1.
						   ]
					ifFalse: [(matchers size == 0) ifTrue: [matchers  := nil]. ret := true. dbFound := false].
	].
	^ret.



	!

match:  block
	| ans dbFound  tmp ret|
	"  Visible for world method for insisting satisfing goal, it is version with posibility to become leaf and to execeute block"
	ret:=false.
	dbFound := true.
	[(dbFound == false) not] whileTrue: 
	[	
		ans := self loop: block. 
		(ans == false) 	ifTrue: [	tmp:= rule eval getVarsList. 
							dbFound := self dbFind. 
							(dbFound == false) ifTrue: [pos:=1. ret:=false. ^false]. 
							chg:= tmp difference: (rule eval getVarsList ). " vars changed by yourself"
							self createMatchers: dbFound.
							pos:=1.
						   ]
					ifFalse: [block value. moje do: [ :x | x  zeros]. matchers := nil. ret:=true. ^true.]. " Return true for futher computation"
	].
	^ret.

	
	




	!

rule
	^rule!

setRule: r setDatabase: db
	rule := r eval.
	database := db.
	dbIndex :=1.
	pos:=1.
	moje := rule eval getVarsList.
	chg := moje.
	! !
!Fitter categoriesFor: #createMatchers:!private! !
!Fitter categoriesFor: #dbFind!private! !
!Fitter categoriesFor: #loop!private! !
!Fitter categoriesFor: #loop:!private! !
!Fitter categoriesFor: #match!public! !
!Fitter categoriesFor: #match:!public! !
!Fitter categoriesFor: #rule!public! !
!Fitter categoriesFor: #setRule:setDatabase:!public! !

Matcher guid: (GUID fromString: '{D4EF1C87-914A-43CC-9C1B-317AE6A08EA4}')!
Matcher comment: 'Object created for every unification process. It encapsulates most of work.

Object vars:
contatiner - during process of unfication we have to unify all terms from set. The successfull unfication means empty set.

Object methods:
chooseAction -> given two terms it tries to unify them.

Privates methods are described in their bodies"'!
!Matcher categoriesForClass!Kernel-Objects! !
!Matcher methodsFor!

chooseAction: terms
	| tmp fst snd err1 err2|
	" Simulates elseifs"
	tmp := self transformTerms: terms.
	fst := tmp car.
	snd := tmp cdr.
	" In fst and snd there are two terms to unify"
	((fst isMemberOf: V) & ((snd isMemberOf: V))) ifTrue: [err1 := fst is: snd. err2:= snd is: fst.  ((err1 == Error) | (err2 == Error)) ifTrue: [^Error]. ^Set new]. " var = var"
	(fst cmp: snd) ifTrue: [^Set new]. " term1 is identical to term2"
	((fst isMemberOf: Pair) & ((snd isMemberOf: C))) ifTrue: [^Error]. " pair == const -> cannot unify"
	((snd isMemberOf: Pair) & ((fst isMemberOf: C) )) ifTrue: [^Error]. "const == pair -> cannot unify"
	((fst isMemberOf: Pair) & (snd isMemberOf: Pair)) ifTrue: [^self makePairs: fst snd: snd]. " take terms from pair and try to unify them separeted"
	" assign value to pair"
	(((fst isMemberOf: V) not) & (snd isMemberOf: V)) ifTrue: 
		[
			err1:= snd is: fst. (err1 == Error) ifTrue: [^Error]. ^Set new
		].
	(((snd isMemberOf: V) not) & (fst isMemberOf: V)) ifTrue: 
		[
			err1:= fst is: snd. (err1 == Error) ifTrue: [^Error]. ^Set new
		].
!

iterate: what
	container := Set new.
	container add: what. " Current set of terms to unify"
	[container isEmpty not] whileTrue: 
		[
			| tmp addition |
			tmp := container anyOne. " Take any term to unify"
			addition := self chooseAction: tmp. " Try to unify"
			container remove: tmp.
			((addition isMemberOf: Matcher) | (addition == Error) ) ifTrue: [^Error].
			container addAll: addition" Pair is separetd into terms"
		].
	^container!

makePairs: t1 snd: t2
	" It extracts terms from two pairs and returns set of that terms"
	| fst1 fst2 snd1 snd2 p1 p2  s|
	fst1 := t1 car.
	fst2 := t2 car.
	snd1 := t1 cdr.
	snd2 := t2 cdr.
	p1 := Pair new car: fst1 cdr: fst2.
	p2 := Pair new car: snd1 cdr: snd2.
	s := Set new.
	s add: p1.
	s add: p2.
	^ s
	
	!

transformTerms: terms
	| term1 term2 t1 t2 tmp |
	term1 := terms car .
	term2 := terms cdr.
	t1 := term1.
	t2 := term2.
	(term1 isMemberOf: V) ifTrue:  
		[
			((term1 isUninitialized) not) ifTrue: [ t1 := term1 val]
		].
	(term2 isMemberOf: V) ifTrue: 
		[
			((term2 isUninitialized) not) ifTrue: [ t2 := term2 val]
		].
	tmp := Pair new.
	tmp car: t1 cdr: t2.
	^tmp! !
!Matcher categoriesFor: #chooseAction:!private! !
!Matcher categoriesFor: #iterate:!public! !
!Matcher categoriesFor: #makePairs:snd:!private! !
!Matcher categoriesFor: #transformTerms:!private! !

Prolog guid: (GUID fromString: '{17422F08-6F55-4B27-A11D-480379BE9DC8}')!
Prolog comment: 'Prolog interpeter. Stores all rules and facts and is obligated to ask for logic questions (go:do)
Prolog objects manages whole processes connected with "prolog" work.

Object methods:
fact: f - add new fact to database, in fact, fact is rule with empty body
head: h body: b - rule addition
go:do - answer the logical question
'!
!Prolog categoriesForClass!Kernel-Objects! !
!Prolog methodsFor!

fact: a
	" Add new fact"
	database addFact:  a!

go: ask do: action
	 | recover matchers tmp i tab|
	" Answert the goal(ask)"
	matchers := Array new.
	((ask class superclass) == Term) ifTrue: [tab:= Array new. tab resize:1. tab at:1 put:ask eval.] " One term"
	ifFalse: [ tab:= ask terms.]. " Conjunction"
	matchers := Array new.
	(tab size > 0) ifTrue: [tab do: [:elem | tmp:= Fitter new. tmp  setRule: (elem eval) setDatabase: database. matchers resize: ((matchers size) + 1). matchers  at: (matchers size) put: tmp ]].
	recover := Array new.
	tab do: [:elem | recover := recover , (elem getVarsList) ].
			i := 1.
			[ (i >= 1) & (i <= (matchers size))] whileTrue: "Try to satify all goals from conjunction"
				[
					| ans|
					(i ==  (matchers size)) 
						ifTrue: [ans := (matchers at: i) match: action. (ans == false) ifTrue: [i :=i - 1]ifFalse: ["one value was found, look for another"] ]
						ifFalse:  
						[	
							ans := (matchers at: i) match. 
							(ans == false) 	ifTrue: [i :=i - 1]
										ifFalse: [i:= i + 1. (i <= (matchers  size)) ifTrue: [(matchers at: i) setRule: ((tab at: i) eval) setDatabase: database ] ] 
						].
				].
		recover do: [ :x | x  hardReset ]. " recover values"
	




!

head: h body: b
	" Add rule in form of head :- body"
	| tmp arr|
	tmp := Pair new.
	((b class superclass) == Term) 	ifTrue: [arr:= Array new:1. arr at:1 put: b]" Only one term in body"
							ifFalse: [arr:= b terms]." list of terms"
	tmp car: h cdr: arr.
	database addRule: tmp!

init
	" Called by new"
	database := Database new! !
!Prolog categoriesFor: #fact:!public! !
!Prolog categoriesFor: #go:do:!public! !
!Prolog categoriesFor: #head:body:!public! !
!Prolog categoriesFor: #init!public! !

!Prolog class methodsFor!

new
	| tmp |
	tmp := super new.
	tmp init.
	^ tmp! !
!Prolog class categoriesFor: #new!public! !

Rule guid: (GUID fromString: '{36A9B98F-A252-4232-B04E-A56905195522}')!
Rule comment: ''!
!Rule categoriesForClass!Kernel-Objects! !
!Rule methodsFor!

body
	^body!

head
	^head!

head: h body: b
	head := h.
	body := b.!

trans
	| dict h b i len tmp r created newHead newBody|
	dict := Dictionary new.
	h := head getVarsList.
	len := h size.
	i := 1.
	[i <= len] whileTrue: [b := (h at:i). ((dict includesKey: b) not) ifTrue: [dict at: b put: (V FreeVar)]. i:=i+1].
	len := body size.
	i := 1.
	[i <= len] whileTrue: [| j vs | b := (body at:i). vs:= b getVarsList. j:=1. [j<= (vs size)] whileTrue: [| t | t:=vs at: j. ((dict includesKey: t) not) ifTrue: [dict at: t put: (V FreeVar)]. j:=j+1]. i:=i+1].
	newHead := head anonim: dict.
	i := 1.
	( len > 0 ) ifFalse: [newBody:= body] ifTrue: [newBody := Array new.].
	[i <= len] whileTrue: [b := (body at:i). newBody resize: ((newBody  size )+ 1). newBody at: (newBody  size) put: (b anonim: dict). i := i + 1].
	tmp := Pair new.
	r := Rule new.
	r head: newHead body: newBody.
	created := dict values.
	tmp car: r cdr: created.
	^tmp


! !
!Rule categoriesFor: #body!public! !
!Rule categoriesFor: #head!public! !
!Rule categoriesFor: #head:body:!public! !
!Rule categoriesFor: #trans!public! !

Term guid: (GUID fromString: '{62967B75-F9E6-4D62-AEE9-C59E8C2C7F33}')!
Term comment: 'Type of abstract class. That''s root class for all types of terms. It provides some basic implemenation of methods, that are common for all terms. Mostly these implementation are only mockups and are overrided in subclasses.

Instance Variables:
type - keeps information about term type (pair, const, var)
value - every term could have another value, so it depends on particular term, what can be stored in value

Instance methods:
% value - that''t shortcut for creating pair with self and value as constant
& term - logical and, allows creating list of terms. It returns conjunction type
, term - creates pair with self and term
@ name - that''t shortcut for creating pair with self and variable name
anonim: dict - needed in second part of task. It replace orginal vars in term with corrospending vars from dict. It works as in PROLOG. During process of goal unification, orginal variables should be replaced with new vars (like _123). In my soultion anonim vars are generated by V and has names from first unused number (as name).
cmp : t - overriding custom default comparision (==). Implemenation depends on term.
eval - initialized values in some cases should be replaced by their values, so that''s what eval is doing
getVarsList - get all vars that occurs in terms (it extract vars recurively from pairs)
go: tern do  block- unificate self with term and if unifciation is possible, execute block
value - interpretation of value - depends on term type



'!
!Term categoriesForClass!Kernel-Objects! !
!Term methodsFor!

% value
	^Pair new car: self cdr: (C % value)!

& t
	| tmp |
	(t isMemberOf: Conjunction) ifTrue: [tmp:=Conjunction new. tmp add: self. tmp := tmp & t .^tmp].
	tmp := Conjunction new.
	tmp add: self.
	tmp add: t.
	^ tmp!

, term
	^ Pair new car: self cdr: term!

@ var
	^Pair new car: self cdr: (V @ var)!

anonim: dict!

cmp: t
	^ self == t!

eval!

getVarsList!

go: t do: action
	" Heart of first part of task - it starts process of unification"
	| m p ans recover|
	m := Matcher new. " Worker that will do work od unification"
	p := Pair new.
	p car: self cdr: t. " car first term cdr second term to unify" 
	ans := m iterate: p. " Loop of unification"
	(ans == Error) ifFalse:
		[action value]. " If success that execute block"
	"Recover initial values of vars"
	recover := self getVarsList , t getVarsList.
	recover do: [ :x | x  zeros]
	
	!

print
	^ value!

value
	^ value! !
!Term categoriesFor: #%!public! !
!Term categoriesFor: #&!public! !
!Term categoriesFor: #,!public! !
!Term categoriesFor: #@!public! !
!Term categoriesFor: #anonim:!public! !
!Term categoriesFor: #cmp:!public! !
!Term categoriesFor: #eval!public! !
!Term categoriesFor: #getVarsList!public! !
!Term categoriesFor: #go:do:!public! !
!Term categoriesFor: #print!public! !
!Term categoriesFor: #value!public! !

C guid: (GUID fromString: '{3BB1F32C-EAB4-4DDF-8F08-09CFABFCC20F}')!
C comment: 'Class reprents Constant values factory. Object are terms of type const. Value is field inherited from Term class ans keeps value of const. Interpretation of const is value  simply value.

Class methods:
% - C is Const values factor, so it creates new constant

Instance methods:
anonim: dict - vars isn''t variable so it doesn''t change value
eval - similar to anonim
cmp: term - if term is const and yours and term values are the same, than consts are equal.
getVarsList - empty array
type: value - inits fields of object'!
!C categoriesForClass!Kernel-Objects! !
!C methodsFor!

== t
	^ value == t value!

anonim: dict
	^self!

cmp: t
	(t isMemberOf: C) ifFalse: [^false].
	^ value == t value!

eval
	^self!

getVarsList
	^ Array new!

printString
	(value==nil) ifTrue: [^'_'].
	^value printString!

type: a value: b
	type := a.
	value := b! !
!C categoriesFor: #==!public! !
!C categoriesFor: #anonim:!public! !
!C categoriesFor: #cmp:!public! !
!C categoriesFor: #eval!public! !
!C categoriesFor: #getVarsList!public! !
!C categoriesFor: #printString!public! !
!C categoriesFor: #type:value:!public! !

!C class methodsFor!

% value
	^super new type: 'const' value: value! !
!C class categoriesFor: #%!public! !

Pair guid: (GUID fromString: '{45D4D19E-B9BE-49FC-9732-6116750CDA47}')!
Pair comment: 'Class reprents pair of terms (Pair(car,cdr)). Interpretation of pair is pair created from car and cdr interpretations.  

Some methods are self explanatory, so the only one interesting thins is that car means first value from pair and cdr means second value.
Methods that are makeing some evaluation (like eval, getVarsList) are returining recurive computation for car and cdr.'!
!Pair categoriesForClass!Kernel-Objects! !
!Pair methodsFor!

anonim: dict
	| tmp |
	tmp := Pair new. 
	tmp car: ((self car) anonim:dict) cdr: ((self cdr) anonim: dict ).
	^tmp.
!

asList
	| tmp |
	tmp := Array new: 2.
	tmp at:1 put: (self car).
	tmp at:2 put: (self cdr).
	^ tmp
	!

car
	^car!

car: a cdr: b
	type := 'pair'.
	car  := a.
	cdr := b!

cdr
	^cdr!

cmp: t
	(t isMemberOf: Pair) ifFalse: [^false].
	^ (self cdr cmp: t cdr) & (self car cmp: t car)
	!

eval
	| tmp |
	tmp := Pair new. tmp car: (self car eval) cdr: (self cdr eval).
	^tmp.
!

getVarsList
	| tmp |
	tmp := Array new.
	tmp := self car getVarsList, self cdr getVarsList.
	^ tmp!

print
	^ #x!

printString
	^'(', car printString , ',' , cdr printString, ')'!

value
	| tmp |
	tmp := Pair new.
	tmp car: car value cdr: cdr value.
	^ tmp! !
!Pair categoriesFor: #anonim:!public! !
!Pair categoriesFor: #asList!public! !
!Pair categoriesFor: #car!public! !
!Pair categoriesFor: #car:cdr:!public! !
!Pair categoriesFor: #cdr!public! !
!Pair categoriesFor: #cmp:!public! !
!Pair categoriesFor: #eval!public! !
!Pair categoriesFor: #getVarsList!public! !
!Pair categoriesFor: #print!public! !
!Pair categoriesFor: #printString!public! !
!Pair categoriesFor: #value!public! !

V guid: (GUID fromString: '{EC35F5AE-BF19-4449-9C3C-2A256F6C6D53}')!
V comment: 'Class reprents Variables factory. Object are terms of type var. Value is field inherited from Term class ans keeps value of var. Interpretation of var is value, but befor assigning value to vars it is nil.


Class methods:
@ name - V is Vars factory, so it creates new variable if variable with name doesn''t exists and in case it was already createg @ returns that variable.
reset - reset state of V as factory
FreeVar - used in second part - it returns first free vars, that can be used as king of anonimous variable - it choose first unused (as name) number.
delete: num - frees number of anonim var


Instance variables:
addr - name of var
refers - set of another vars, that refers to self. It is needed in case when we unify: x = y and both vars doesn''t have any concrete value. So if after unficiation vars points at another vars, that doesn''t have concreate value, than value is nil. Information about x =y is only included in refers. When assigining value to var, that have vars on refers list, value should be assigined to every var on refers (it work recurively). So if x = y = z = q, and after some step
y = 1, than x = 1, y =1 , z = 1, q = 1 and refers aren''t up to date any more. The process of passing value is implemented in is:
	







'!
!V categoriesForClass!Kernel-Objects! !
!V methodsFor!

addr: c
	type := 'var'.
	addr:= c.
	refers := Set new!

anonim: dict
	"replace with value assigned to self addr"
	^(dict at: self)!

canBind
	" The same meaning as isUninitialized, but it was used in other semtanic context"
	(value == nil) ifTrue: [^true] ifFalse: [false]!

car
	^value car!

cdr
	^value cdr!

eval
	((value == nil) not) ifTrue: [^self val eval] ifFalse: [^self]!

getVarsList
	| tmp |
	tmp := Array new: 1.
	tmp at:1 put: self.
	^ tmp!

hardReset
	" At the contrary to zeros, it clean refers"
	self zeros.
	refers := Set new.!

is: v
	| list |
	(v isMemberOf: V) ifTrue: [^refers add: v].
	((value == nil) not)
			ifTrue:	[
						((value cmp: v ) not) ifTrue: [^Error] ifFalse: [^self]
					].
	list := v getVarsList.
	((list indexOf: self) > 0) ifTrue: [^Error].
	value := v.
	refers do: [:el | el is: v]." Pass value to another vars in chains, that point on each other"
	"refers := Set new."


!

isUninitialized
	^(value == nil) ifTrue: [true] ifFalse: [false]!

printString
	(value==nil) ifTrue: [ ^addr printString, '=' , '*'].^addr printString, '=' , value!

val
	" Raw value - not interpretation"
	^value!

value
	" Interpretation of value"
	^ value value!

zeros
	value := nil.
	refers do: [:el | (el isUninitialized not)  ifTrue: [el zeros]].
	"refers := Set new"
	! !
!V categoriesFor: #addr:!public! !
!V categoriesFor: #anonim:!public! !
!V categoriesFor: #canBind!public! !
!V categoriesFor: #car!public! !
!V categoriesFor: #cdr!public! !
!V categoriesFor: #eval!public! !
!V categoriesFor: #getVarsList!public! !
!V categoriesFor: #hardReset!public! !
!V categoriesFor: #is:!public! !
!V categoriesFor: #isUninitialized!public! !
!V categoriesFor: #printString!public! !
!V categoriesFor: #val!public! !
!V categoriesFor: #value!public! !
!V categoriesFor: #zeros!public! !

!V class methodsFor!

@ var
	^self var: var!

delete: bag
	UsedVars := UsedVars - bag.!

FreeVar
	| v |
	(UsedVars == nil) ifTrue: [UsedVars := Set new. Index:=0].
	[(UsedVars includes: Index) ] whileTrue: [Index := Index + 1]. " Look for first free numer for name"
	v := V @ Index.
	Index := Index + 1. " Counter of first free number - kinf of heuristic"
	^v.!

getVar: var
	^VarsDict!

reset
	VarsDict:= Dictionary new.
	UsedVars:= Set new.
	Index :=0.!

var: i
	| tmp arr|
	(VarsDict == nil) ifTrue: [VarsDict  := Dictionary  new. UsedVars := Set new. Index:=0].
	tmp := VarsDict includesKey: i.
	UsedVars add: i.
	(tmp) ifTrue: 
			[arr := VarsDict at:i]
			ifFalse:
			[arr :=VarsDict at: i put: (V new addr: i )].
	^arr
	! !
!V class categoriesFor: #@!public! !
!V class categoriesFor: #delete:!public! !
!V class categoriesFor: #FreeVar!public! !
!V class categoriesFor: #getVar:!public! !
!V class categoriesFor: #reset!public! !
!V class categoriesFor: #var:!public! !

"Binary Globals"!

