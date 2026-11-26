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
  ![![2, 0, 0, 0, 0], ![-14, 5, 1, 0, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![14, -4, 2, -2, 12]], ![![14, -4, 2, -2, 12], ![13, 1, 4, -1, 12]]]
 hmul := by decide
 f := ![![![![-4081188906423, 317518993956, 730583512435, -434606084733, 4385377550042], ![-862952717680, 196476917838, 0, -210026688, 4123905]], ![![0, 0, 0, 0, 0], ![220930, 2043, 0, -75, -2]]], ![![![37400050586767, -2909746818497, -6695073653663, 3982733935399, -40187637959141], ![7908106200272, -1800516181626, 0, 1924686393, -37791501]], ![![0, 0, 0, 0, 0], ![-2024608, -18721, 0, 687, 19]]]]
 g := ![![![![36, -28, 20, -18, 110], ![-8, -4, 0, 0, 0]], ![![8154, -6850, 5066, -4516, 27793], ![-2134, -1004, 0, 0, 6]]], ![![![8154, -6850, 5066, -4516, 27793], ![-2134, -1004, 0, 0, 6]], ![![4138, -3468, 2564, -2285, 14062], ![-1078, -508, 0, 0, 3]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![-14, 5, 1, 0, 5]] ![![2, 0, 0, 0, 0], ![7, -2, 1, -1, 6]]
  ![![10068117025306292741207, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![14, -4, 2, -2, 12]], ![![-28, 10, 2, 0, 10], ![100, -9, -5, 0, -31]]]
 hmul := by decide
 f := ![![![![852781845548739774328196095651420, -66347039300666838740629602766563, -152658573497052141706640633713436, 90812799656296532165301047051919, -916343419600237318536916963756307], ![180317553343869756342594205894942, -41054683515329235001662460541142, 0, 43890202507980661728136358433, -866393736275701275854582193]], ![![0, 0, 0, 0, 0], ![19725202805340222696488894, -121543939919432910848050, 0, 0, 95164177111163560079]]]]
 g := ![![![![2331818, -3899479, 1650979, -1459514, 9959720]], ![![-68914790, 14613947, 3848794, 645823, 15098536]]], ![![![61171870, 2205849, -11351441, 5821094, -59996934]], ![![427131140, -133752634, -1275937, -22243613, 39070893]]]]
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

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-14, 5, 1, 0, 5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
