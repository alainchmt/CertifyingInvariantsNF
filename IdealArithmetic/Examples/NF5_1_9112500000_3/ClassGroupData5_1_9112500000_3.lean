import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_9112500000_3.RI5_1_9112500000_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-1228505867337897533374795968991419416, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-68078, 251247, 79053, 269863, 369426]

def zeta2 := B.equivFun.symm ![72669884397944627058787560488909268342246905518, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![12, 1, 1, 2, 4]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![12, 1, 1, 2, 4]] ![![2, 0, 0, 0, 0], ![12, 1, 1, 2, 4]]
  ![![-1228505867337897533374795968991419416, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![24, 2, 2, 4, 8]], ![![24, 2, 2, 4, 8], ![120, 0, 6, 0, 0]]]
 hmul := by decide
 f := ![![![![135434436876205926301952382570460276, -77114784735384055776484231182701009, -13204485277102510895085654282325954, -131677955964191991177199707010857567, -258899141265201183464404572057325680], ![117970747756397916369920501564739310, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![-38346179674968926928839146140225033, 0, 0, 0, 0]]]]
 g := ![![![![-49349175729458, 43142503703126, 401320779173, 7949918990943, -3275653936058]], ![![18017307334872, -64936005697627, -20283940088445, -69316999380318, -94732007879986]]], ![![![18017307334872, -64936005697627, -20283940088445, -69316999380318, -94732007879986]], ![![1291739434286880, -1035429841960950, 27918381914379, -81371092553280, 268776976414620]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-182324, -9067, -6907, -7553, -13056])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![32707014916392676823502412576923329918983295903666307693559684, 1930666925071420710533004967825244597131962159044631410841767, 1250062892720242287645494217143430672681366570779776837805005, 1459730474990433573349477125828298890409219249172968005906833, 2444843226337328222198209297348857493679866448050357471912496])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![12, 1, 1, 2, 4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
