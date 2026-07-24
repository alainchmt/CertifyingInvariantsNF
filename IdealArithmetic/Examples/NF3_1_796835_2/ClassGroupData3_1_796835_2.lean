import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_796835_2.RI3_1_796835_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-1101, 16, -47]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![2108971976667486228034948427966569287, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![3, 4, 9]]]
 hmul := by decide
 f := ![![![![40, 41, 117], ![22, -24, 0]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![12570, 13105, 36765], ![6553, -7542, 0]], ![![0, 0, 0], ![-1257, 1, 0]]]]
 g := ![![![![-8, -12, -27], ![0, 12, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-6, -8, -18], ![0, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![-1101, 16, -47]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![0, 2, 0], ![3, 4, 9]]]
 hmul := by decide
 f := ![![![![2091210, 2129232, 6266477], ![1064616, -1330770, 0]], ![![495582, -114066, 0], ![-19011, 16, 0]]]]
 g := ![![![![-36, -7, -1]], ![![60, -22, -30]]], ![![![30, -11, -15]], ![![1041, 143, -27]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1268931921909920393400883596748155124053168001696263103410844116739145327559, -18435509837542608693053064051473038662865240710636200526114390194235803706, 54170867658322082695028258417334988710372068805080605834671539586268008866])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
