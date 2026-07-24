import IdealArithmetic.Examples.NF3_3_866133_1.PrimesBelow3_3_866133_1F0
import IdealArithmetic.Examples.NF3_3_866133_1.PrimesBelow3_3_866133_1F1
import IdealArithmetic.Examples.NF3_3_866133_1.PrimesBelow3_3_866133_1F2
import IdealArithmetic.Examples.NF3_3_866133_1.PrimesBelow3_3_866133_1F3
import IdealArithmetic.Examples.NF3_3_866133_1.PrimesBelow3_3_866133_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 206]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 207 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB207I0
  exact PB207I1
  exact PB207I2
  exact PB207I3
  exact PB207I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB207 : PrimesBelowBoundCertificate O 207 := by
  refine primesBelowBoundCertificate_of_Interval O eC 206 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 206 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 206 hC

lemma cert_eq_𝔭 : PB207.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 206 rfl rfl hel hC
