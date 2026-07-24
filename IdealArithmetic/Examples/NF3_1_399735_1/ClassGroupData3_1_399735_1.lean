import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_399735_1.RI3_1_399735_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![4445973603914535301, 311037384426852398, -92825645688721961]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-942025009646687929027826020612227395622105483608343710519012972635803723986249492287, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-51, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-51, -2, 1]] ![![2, 0, 0], ![-51, -2, 1]]
  ![![4, 0, 0], ![-51, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-102, -4, 2]], ![![-102, -4, 2], ![681, 58, -13]]]
 hmul := by decide
 f := ![![![![76, 1416, 439], ![-2644, -348, 0]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![-284637, -7089178, -2200730], ![13247607, 1743153, 0]], ![![0, 0, 0], ![20019, -4, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![21, 30, 4], ![94, 12, 0]]], ![![![21, 30, 4], ![94, 12, 0]], ![![159, -383, -67], ![-1311, -174, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-51, -4, 1]] ![![2, 0, 0], ![-51, -2, 1]]
  ![![4445973603914535301, 311037384426852398, -92825645688721961]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-204, -8, 4]], ![![-102, -8, 2], ![-87, 12, -3]]]
 hmul := by decide
 f := ![![![![-16843343209269233604570976, -412622058089811458335436412, -129716978594235594735302223], ![777268820629059117884345244, 102830075938667827574549032, 0]], ![![-7310936807224974961711212, 6387865681047028266858, 0], ![362761040463648497797, 311037384426852398, 0]]]]
 g := ![![![![-242445084284766977906286335964645400, -69708976180782137013816776806531318, -9071733793944566647142303641271429]], ![![-1976455112136541981288552682383212252, -568279875588172164399748900951736186, -73954374805652079478593476943794411]]], ![![![753545332369085805607045957932508242, 216662976608582007851584644278034568, 28195921880983813950948886513998398]], ![![6143034529989380628778021142040599637, 1766274820510591098637126337778887688, 229858130996861278487845779467145273]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-7455829881213704767223598633450540816255679, -580712640677966609083116366765800272920124, 164510094348332241484760411115868811088814])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-51, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-51, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
