import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_10125000000_1.RI5_1_10125000000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![10068117025306292741207, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-2288805750138070, 620125621715449, 93403693655176, 22466222402355, 682300270585169]

def zeta2 := B.equivFun.symm ![-54324600083209633790, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -2, 1, -1, 6]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![7, -2, 1, -1, 6]] ![![2, 0, 0, 0, 0], ![7, -2, 1, -1, 6]]
  ![![2, 0, 0, 0, 0], ![1, 1, 2, -1, 10]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![14, -4, 2, -2, 12]], ![![14, -4, 2, -2, 12], ![13, 1, 4, -1, 12]]]
 hmul := by decide
 f := ![![![![-4081188906423, 317518993956, 730583512435, -434606084733, 4385377550042], ![-862952717680, 196476917838, 0, -210026688, 4123905]], ![![0, 0, 0, 0, 0], ![220930, 2043, 0, -75, -2]]], ![![![-641789403840, 49931608293, 114888275857, -68344197348, 689624741215], ![-135704061467, 30897076038, 0, -33027852, 648507]], ![![0, 0, 0, 0, 0], ![34739, 322, 0, -12, 0]]]]
 g := ![![![![-2081, 607, 42, 79, 120], ![-130, 44, 0, 0, 4]], ![![-9262, 2700, 186, 352, 529], ![-578, 196, 0, 0, 18]]], ![![![-9262, 2700, 186, 352, 529], ![-578, 196, 0, 0, 18]], ![![-6032, 1764, 123, 230, 347], ![-379, 128, 0, 0, 12]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![1, 1, 2, -1, 10]] ![![2, 0, 0, 0, 0], ![7, -2, 1, -1, 6]]
  ![![10068117025306292741207, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![14, -4, 2, -2, 12]], ![![2, 2, 4, -2, 20], ![25, 17, 4, 1, 4]]]
 hmul := by decide
 f := ![![![![-89431642228285188234682351940645, 6957825060070197907140991837140, 16009371589739123744659875932899, -9523580525028542008589476928622, 96097358976453327522688778567767], ![-18910019872324541283838211495295, 4305426728362777057456376876799, 0, -4602334202357849509688096301, 93140644682593361124156846]], ![![0, 0, 0, 0, 0], ![5298929661380904404862889, 355927775796719739009832, 0, 0, -9147518216122871704774]]]]
 g := ![![![![2331818, -3899479, 1650979, -1459514, 9959720]], ![![-68914790, 14613947, 3848794, 645823, 15098536]]], ![![![-81345296, 33101087, -3746963, 7451962, -30888400]], ![![204419729, -1156113, -33487765, 15889884, -174522998]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![344412118014352214, 31492024271224303, 28236629471802842, -8140500563315459, 97072938388913653])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-778559803182313074925274, 103413255323453356813642, 75739613518786416371803, -18704694124197856516081, 360078571582185268860887])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -2, 1, -1, 6]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 2, -1, 10]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
