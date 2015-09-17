#!/bin/sh

set -e

if [ $# != 1 ]; then
	echo "Usage: ${0##*/} PROGRAM" >&2
	exit 1
fi

PROGRAM="$1"

t(){
	printf "%s...\\n" "$1"
	tee "$1" | time -p "$PROGRAM"
	printf "Done\\n"
}

cat << EOF | t positive-implicational.pa
axiomatization
	implies :: "prop => (prop => prop)" (infixr "-->" 25)
where
	MP: [| "A --> B"; "A" |] ==> "B"

allow_deduction implies

lemma A1: "A --> (B --> A)"
proof
	{
		assume a: "A"
		{
			assume "B"
			have "A" by a
		}
	}
	show by this
qed

lemma A2: "(A --> (B --> C)) --> ((A --> B) --> (A --> C))"
proof
	{
		assume abc: "A --> (B --> C)"
		{
			assume ab: "A --> B"
			{
				assume "A"
				have b: "B" by MP(ab, this)
				have bc: "B --> C" by MP(abc, assm)
				have "C" by MP(bc, b)
			}
		}
	}
	show by this
qed

lemma a_impl_a: "A --> A"
proof
	{
		assume "A"
	}
	show by this
qed

lemma syllogism: "(A --> B) --> ((B --> C) --> (A --> C))"
proof
	{
		assume ab: "A --> B"
		{
			assume bc: "B --> C"
			{
				assume "A"
				have "B" by MP(ab, this)
				have "C" by MP(bc, this)
			}
		}
	}
	show by this
qed

lemma swap_premises: "(A --> (B --> C)) --> (B --> (A --> C))"
proof
	{
		assume abc: "A --> (B --> C)"
		{
			assume b: "B"
			{
				assume "A"
				have "B --> C" by MP(abc, this)
				have "C" by MP(this, b)
			}
		}
	}
	show by this
qed

lemma reverse_syllogism: "(B --> C) --> ((A --> B) --> (A --> C))" by MP(swap_premises, syllogism)
EOF

cat positive-implicational.pa - << EOF | t positive.pa
axiomatization
	conj :: "prop => (prop => prop)" (infixl "&" 35) and
	disj :: "prop => (prop => prop)" (infixl "|" 30)
where
	A3: "A & B --> A" and
	A4: "A & B --> B" and
	A5: "A --> (B --> A & B)" and
	A6: "A --> A | B" and
	A7: "B --> A | B" and
	A8: "(A --> C) --> ((B --> C) --> (A | B --> C))"
EOF

cat positive.pa - << EOF | t minimal.pa
axiomatization
	Not :: "prop => prop" (prefix "~" 40)
where
	A9: "(A --> B) --> ((A --> ~B) --> ~A)"

lemma contraposition: "(A --> B) --> (~B --> ~A)"
proof
	{
		assume "A --> B"
		have "(A --> ~B) --> ~A" by MP(A9, this)
		have "~B --> ~A" by MP(MP(syllogism, A1), this)
	}
	show by this
qed

lemma intro_2_neg: "A --> ~~A"
proof
	{
		assume "A"
		have "~A --> A" by MP(A1, this)
		have "~~A" by MP(MP(A9, this), a_impl_a)
	}
	show by this
qed

lemma elim_3_neg: "~~~A --> ~A"
proof
	have a: "(A --> ~~~A) --> ~A" by MP(A9, intro_2_neg)
	{
		assume "~~~A"
		have "A --> ~~~A" by MP(A1, this)
		have "~A" by MP(a, this)
	}
	show by this
qed

lemma ex_falso_not: "A --> (~A --> ~B)"
proof
	{
		assume "A"
		have ba: "B --> A" by MP(A1, this)
		{
			assume "~A"
			have "B --> ~A" by MP(A1, this)
			have "~B" by MP(MP(A9, ba), this)
		}
	}
	show by this
qed
EOF

cat positive.pa - << EOF | t alt-minimal.pa
axiomatization
	Not :: "prop => prop" (prefix "~" 40)
where
	contraposition: "(A --> B) --> (~B --> ~A)" and
	intro_2_neg: "A --> ~~A"

lemma a_impl_not_b_impl_b_impl_not_a: "(A --> ~B) --> (B --> ~A)"
proof
	have "B --> ~~B" by intro_2_neg
	have a: "(~~B --> ~A) --> (B --> ~A)" by MP(syllogism, this)
	have "(A --> ~B) --> (~~B --> ~A)" by contraposition
	show by MP(MP(syllogism, this), a)
qed

lemma not_a_impl_b_impl_not_b_impl_a: "A --> (~B --> ~(A --> B))"
proof
	have a: "A --> ((A --> B) --> B)" by MP(swap_premises, a_impl_a)
	have "((A --> B) --> B) --> (~B --> ~(A --> B))" by contraposition
	show by MP(MP(syllogism, a), this)
qed

lemma a_impl_not_a_impl_not_a: "(A --> ~A) --> ~A"
proof
	have a: "A --> (~~A --> ~(A --> ~A))" by not_a_impl_b_impl_not_b_impl_a
	have "A --> ~~A" by intro_2_neg
	have "A --> ~(A --> ~A)" by MP(MP(A2, a), this)
	show by MP(a_impl_not_b_impl_b_impl_not_a, this)
qed

lemma A9: "(A --> B) --> ((A --> ~B) --> ~A)"
proof
	{
		assume "A --> B"
		have "(B --> ~A) --> (A --> ~A)" by MP(syllogism, this)
		have "(A --> ~B) --> (A --> ~A)" by MP(MP(syllogism, a_impl_not_b_impl_b_impl_not_a), this)
		have "(A --> ~B) --> ~A" by MP(MP(syllogism, this), a_impl_not_a_impl_not_a)
	}
	show by this
qed
EOF

# Эквивалентность minimal и alt-minimal доказана

# Если к positive добавить константу False и никаких аксиом, получится логика, эквивалентная minimal, я не буду это доказывать

cat minimal.pa - << EOF | t intuitionistic.pa
axiomatization where
	ex_falso: "A --> (~A --> B)"

lemma plan_b: "A | B --> (~A --> B)" by MP(MP(A8, ex_falso), A1)

lemma not_a_or_b_impl_a_impl_b: "~A | B --> (A --> B)" by MP(MP(A8, MP(swap_premises, ex_falso)), A1)
EOF

# Будем называть vml2010 конспекты лекций 1 - 8 курса "Введение в математическую логику" Л. Д. Беклемишева ( http://lpcs.math.msu.su/vml2010/ , URI нужно набирать с конечным слешем). Также будем называть vml2010 формулировку классического исчисления высказываний, введённую в этих конспектах (10 аксиом A1 - A10 и MP)

cat intuitionistic.pa - << EOF | t alt-classical.pa
# Альтернативная к vml2010 формулировка классического исчисления

axiomatization where
	excluded_middle: "A | ~A"

lemma A10: "~~A --> A"
proof
	have "A | ~A --> (~~A --> A)" by MP(MP(A8, A1), ex_falso)
	show by MP(this, excluded_middle)
qed
EOF

cat minimal.pa - << EOF | t classical.pa
# vml2010

axiomatization where
	A10: "~~A --> A"

# Это правило формализует "классическое рассуждение", противопоставленное интуиционистскому. Это формализация рассуждения "Если sqrt(2)^sqrt(2) рационально, то существуют рациональные числа вида a^b, где a и b иррациональны. Если иррационально - то тоже существуют. Значит, они существуют", которое обычно приводят в пример "неправильного" рассуждения интуционисты

lemma classical_reasoning: "(A --> B) --> ((~A --> B) --> B)"
proof
	{
		assume "A --> B"
		have "~B --> ~A" by MP(contraposition, this)
		have a: "(~B --> ~~A) --> ~~B" by MP(A9, this)
		{
			assume "~A --> B"
			have "~B --> ~~A" by MP(contraposition, this)
			have "~~B" by MP(a, this)
			have "B" by MP(A10, this)
		}
	}
	show by this
qed

lemma ex_falso: "A --> (~A --> B)"
proof
	have a: "A --> (~B --> A)" by A1
	have "(~B --> A) --> ((~B --> ~A) --> ~~B)" by A9
	have "A --> ((~B --> ~A) --> ~~B)" by MP(MP(syllogism, a), this)
	have b: "(~B --> ~A) --> (A --> ~~B)" by MP(swap_premises, this)
	have "~A --> (~B --> ~A)" by A1
	have c: "~A --> (A --> ~~B)" by MP(MP(syllogism, this), b)
	have "~~B --> B" by A10
	have "(A --> ~~B) --> (A --> B)" by MP(reverse_syllogism, this)
	have "~A --> (A --> B)" by MP(MP(syllogism, c), this)
	show by MP(swap_premises, this)
qed

lemma excluded_middle: "A | ~A" by MP(MP(classical_reasoning, A6), A7)

lemma plan_b: "A | B --> (~A --> B)" by MP(MP(A8, ex_falso), A1)
EOF

# Эквивалентность classical и alt-classical доказана

cat classical.pa - << EOF | t false.pa
axiomatization
	False :: "prop" ("FALSE")
where
	not_false: "~ False"

lemma false_impl_a: "False --> A"
proof
	{
		assume "False"
		have "A" by MP(MP(ex_falso, this), not_false)
	}
	show by this
qed

lemma contradiction2: "(A --> False) --> ~A"
proof
	{
		assume "A --> False"
		have "A --> ~False" by MP(A1, not_false)
		have "~A" by MP(MP(A9, assm), this)
	}
	show by this
qed

lemma contradiction: "(~A --> False) --> A"
proof
	{
		assume "~A --> False"
		have "~~A" by MP(contradiction2, this)
		have "A" by MP(A10, this)
	}
	show by this
qed
EOF

cat false.pa - << EOF | t modal-k.pa
# Нельзя использовать дедукцию из-за Necessitation Rule
deny_deduction

axiomatization
	box :: "prop => prop" (prefix "[]" 50)
where
	# Distribution Axiom
	dist: "[](A --> B) --> ([]A --> []B)" and

	# Necessitation Rule
	nec: "A" ==> "[]A"
EOF

cat false.pa - << EOF | t fol.pa
# Типа FOL, с функциями высшего порядка

axiomatization
	All :: "('a => prop) => prop" (binder "!") and
	Ex :: "('a => prop) => prop" (binder "?")
where
	spec: "All A --> A t" and
	exI: "A t --> Ex A"

allow_fixing All
allow_obtaining Ex
EOF

cat fol.pa - << EOF | t eq.pa
axiomatization
	eq :: "'a => ('a => prop)" (infix "=" 50)
where
	refl: "a = a" and
	subst: "s = t --> (P s --> P t)" and
	ext: "(! x. f x = g x) --> f = g"

lemma eq_commute: "(a::'a) = b --> b = a"
proof
	{
		assume "a = b"
		have "a = b --> ((%x. x = a) a --> (%x. x = a) b)" by subst
		have "a = b --> (a = a --> b = a)" by this
		have "b = a" by MP(MP(this, assm), refl)
	}
	show by this
qed

lemma trans: "(r::'a) = s --> (s = t --> r = t)"
proof
	have "s = r --> ((%x. x = t) s --> (%x. x = t) r)" by subst
	have "s = r --> (s = t --> r = t)" by this
	show by MP(MP(syllogism, eq_commute), this)
qed

lemma arg_cong: "(x::'a) = y --> ((f x)::'b) = f y"
proof
	{
		assume "x = y"
		have a: "y = x" by MP(eq_commute, this)
		have "y = x --> ((%z. f z = f y) y --> (%z. f z = f y) x)" by subst
		have "y = x --> (f y = f y --> f x = f y)" by this
		have "f x = f y" by MP(MP(this, a), refl)
	}
	show by this
qed

lemma fun_cong: "(f :: 'a => 'b) = g --> f x = g x"
proof
	have "f = g --> (%h. h x) f = (%h. h x) g" by arg_cong
	show by this
qed

axiomatization
	comp :: "('b => 'c) => (('a => 'b) => ('a => 'c))"
where
	comp_def: "comp f g x = f (g x)"

lemma comp_assoc: "comp (comp (f :: 'c => 'd) (g :: 'b => 'c)) (h :: 'a => 'b) = comp f (comp g h)"
proof
	{
		fix x :: "'a"
		have "comp (comp f g) h x = comp f g (h x)" by comp_def
		have "comp (comp f g) h x = f (g (h x))" by MP(MP(trans, this), comp_def)
		have "comp (comp f g) h x = f (comp g h x)" by MP(MP(trans, this), MP(arg_cong, MP(eq_commute, comp_def)))
		have "comp (comp f g) h x = comp f (comp g h) x" by MP(MP(trans, this), MP(eq_commute, comp_def))
	}
	show by MP(ext, this)
qed
EOF

cat eq.pa - << EOF | t pa.pa
typedecl i

axiomatization
	zero :: "i" ("0") and
	succ :: "i => i" (prefix "SUCC " 999)
where
	PA1: "~ succ a = 0" and
	PA2: "a = 0 | ? b. a = succ b" and
	PA3: "succ a = succ b --> a = b" and
	PA4: "P 0 --> ((! x. P x --> P (succ x)) --> P x)"

axiomatization
	plus :: "i => (i => i)" (infixl "+" 65)
where
	plus_zero: "a + 0 = a" and
	plus_succ: "a + succ b = succ (a + b)"

lemma zero_plus_a: "0 + a = a"
proof
	have base: "(%x. 0 + x = x) 0" by plus_zero
	{
		fix x :: "i"
		have a: "0 + succ x = succ (0 + x)" by plus_succ
		{
			assume "0 + x = x"
			have "succ (0 + x) = succ x" by MP(arg_cong, assm)
			have "0 + succ x = succ x" by MP(MP(trans, a), this)
		}
	}
	show by MP(MP(PA4, base), this)
qed

lemma succ_a_plus_b: "succ a + b = succ (a + b)"
proof
	have "succ a + 0 = succ a" by plus_zero
	have base: "(%x. succ a + x = succ (a + x)) 0" by MP(MP(trans, this), MP(arg_cong, MP(eq_commute, plus_zero)))
	{
		fix x :: "i"
		{
			assume "succ a + x = succ (a + x)"
			have "succ a + succ x = succ (succ a + x)" by plus_succ
			have "succ a + succ x = succ (succ (a + x))" by MP(MP(trans, this), MP(arg_cong, assm))
			have "succ a + succ x = succ (a + succ x)" by MP(MP(trans, this), MP(arg_cong, MP(eq_commute, plus_succ)))
		}
	}
	show by MP(MP(PA4, base), this)
qed

lemma plus_commute: "a + b = b + a"
proof
	have base: "(%x. x + b = b + x) 0" by MP(MP(trans, zero_plus_a), MP(eq_commute, plus_zero))
	{
		fix x :: "i"
		{
			assume "x + b = b + x"
			have "succ x + b = succ (x + b)" by succ_a_plus_b
			have "succ x + b = succ (b + x)" by MP(MP(trans, this), MP(arg_cong, assm))
			have "succ x + b = b + succ x" by MP(MP(trans, this), MP(eq_commute, plus_succ))
		}
	}
	show by MP(MP(PA4, base), this)
qed

axiomatization
	le :: "i => (i => prop)" (infix "<=" 50)
where
	LE1: "a <= 0 --> a = 0" and
	LE2: "a = 0 --> a <= 0" and
	LE3: "a <= succ b --> a = succ b | a <= b" and
	LE4: "a = succ b --> a <= succ b" and
	LE5: "a <= b --> a <= succ b"

axiomatization
	less :: "i => (i => prop)" (infix "<" 50)
where
	L1: "a < b --> a <= b" and
	L2: "a < b --> ~(a = b)" and
	L3: "a <= b --> (~(a = b) --> a < b)"

lemma less_zero: "~ a < 0"
proof
	{
		assume "a < 0"
		have "a <= 0" by MP(L1, this)
		have "a = 0" by MP(LE1, this)
		have "False" by MP(MP(ex_falso, this), MP(L2, assm))
	}
	show by MP(contradiction2, this)
qed

lemma less_succ: "a < succ b --> a <= b"
proof
	{
		assume "a < succ b"
		have "a <= succ b" by MP(L1, assm)
		have a: "a = succ b | a <= b" by MP(LE3, this)
		have "~(a = succ b)" by MP(L2, assm)
		have "a <= b" by MP(MP(plan_b, a), this)
	}
	show by this
qed

lemma le: "a <= b --> a < b | a = b"
proof
	{
		assume a: "a <= b"
		have switch: "b = 0 | ? x. b = succ x" by PA2
		{
			assume "b = 0"
			have "a <= 0" by MP(MP(subst, this), a)
			have "a = 0" by MP(LE1, this)
			have "a = b" by MP(MP(trans, this), MP(eq_commute, assm))
			have "a < b | a = b" by MP(A7, this)
		}
		note casea = this
		{
			assume "? x. b = succ x"
			{
				obtain x :: "i" where "b = succ x" by this
				have "a <= succ x" by MP(MP(subst, this), a)
				have b: "a = succ x | a <= x" by MP(LE3, this)
				{
					assume "a = succ x"
					have "a = b" by MP(MP(trans, this), MP(eq_commute, obtaining))
					have "a < b | a = b" by MP(A7, this)
				}
				note casea2 = this
				{
					assume "~(a = succ x)"
					have "a <= x" by MP(MP(plan_b, b), this)
					have "a <= succ x" by MP(LE5, this)
					have "a < succ x" by MP(MP(L3, this), assm)
					have "a < b" by MP(MP(subst, MP(eq_commute, obtaining)), this)
					have "a < b | a = b" by MP(A6, this)
				}
				note caseb2 = this
				have "a < b | a = b" by MP(MP(classical_reasoning, casea2), caseb2)
			}
		}
		note caseb = this
		have "a < b | a = b" by MP(MP(MP(A8, casea), caseb), switch)
	}
	show by this
qed

lemma full_induction: "(! x. (! y. y < x --> P y) --> P x) --> P a"
proof
	{
		assume "! x. (! y. y < x --> P y) --> P x"
		{
			fix t :: "i"
			have "t < 0 --> P t" by MP(MP(swap_premises, ex_falso), less_zero)
		}
		have base: "(%z. (! t. t < z --> P t)) 0" by this
			{
				fix z :: "i"
				have a: "(! y. y < z --> P y) --> P z" by MP(spec, assm)
				{
					assume "! t. t < z --> P t"
					have pz: "P z" by MP(a, this)
					{
						fix t :: "i"
						have casea: "t < z --> P t" by MP(spec, assm)
						{
							assume "t < succ z"
							have "t <= z" by MP(less_succ, this)
							have switch: "t < z | t = z" by MP(le, this)
							{
								assume "t = z"
								have "P t" by MP(MP(subst, MP(eq_commute, this)), pz)
							}
							note caseb = this
							have "P t" by MP(MP(MP(A8, casea), caseb), switch)
						}
						have "t < succ z --> P t" by this
					}
					have "! t. t < succ z --> P t" by this
				}
				have "(! t. t < z --> P t) --> (! t. t < succ z --> P t)" by this
			}
		have "! t. t < a --> P t" by MP(MP(PA4, base), this)
		have "P a" by MP(MP(spec, assm), this)
	}
	show by this
qed

axiomatization
	one :: "i" ("1") and
	two :: "i" ("2") and
	three :: "i" ("3") and
	four :: "i" ("4")
where
	one_def: "1 = succ 0" and
	two_def: "2 = succ 1" and
	three_def: "3 = succ 2" and
	four_def: "4 = succ 3"

lemma two_plus_two: "2 + 2 = 4"
proof
	have "2 + 2 = 2 + succ 1" by MP(arg_cong, two_def)
	have "2 + 2 = succ (2 + 1)" by MP(MP(trans, this), plus_succ)
	have "2 + 2 = succ (2 + succ 0)" by MP(MP(trans, this), MP(arg_cong, MP(arg_cong, one_def)))
	have "2 + 2 = succ (succ (2 + 0))" by MP(MP(trans, this), MP(arg_cong, plus_succ))
	have "2 + 2 = succ (succ 2)" by MP(MP(trans, this), MP(arg_cong, MP(arg_cong, plus_zero)))
	have "2 + 2 = succ 3" by MP(MP(trans, this), MP(arg_cong, MP(eq_commute, three_def)))
	show by MP(MP(trans, this), MP(eq_commute, four_def))
qed

axiomatization
	times :: "i => (i => i)" (infixl "*" 70)
where
	times_zero: "a * 0 = 0" and
	times_succ: "a * succ b = a * b + a"
EOF

cat eq.pa - << EOF | t group.pa
typedecl i

axiomatization
	e :: "i" and
	times :: "i => (i => i)" (infixl "*" 70) and
	inv :: "i => i"
where
	assoc: "(a * b) * c = a * (b * c)" and
	e1: "a * e = a" and
	e2: "e * a = a" and
	inv1: "a * inv a = e" and
	inv2: "inv a * a = e"

lemma one_e: "i * a = e --> a * i = e --> j * a = e --> a * j = e --> i = j"
proof
	{
		assume iae: "i * a = e"
		{
			assume aie: "a * i = e"
			{
				assume jae: "j * a = e"
				{
					assume aje: "a * j = e"
					have "i = i * e" by MP(eq_commute, e1)
					have "i = i * (a * j)" by MP(MP(trans, this), MP(arg_cong, MP(eq_commute, aje)))
					have "i = (i * a) * j" by MP(MP(trans, this), MP(eq_commute, assoc))
					have "i = e * j" by MP(MP(trans, this), MP(fun_cong, MP(arg_cong, iae)))
					have "i = j" by MP(MP(trans, this), e2)
				}
			}
		}
	}
	show by this
qed
EOF
