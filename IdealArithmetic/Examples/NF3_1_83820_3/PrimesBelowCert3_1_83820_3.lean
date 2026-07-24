import IdealArithmetic.Examples.NF3_1_83820_3.PrimesBelow3_1_83820_3F0
import IdealArithmetic.Examples.NF3_1_83820_3.PrimesBelow3_1_83820_3F1

noncomputable section
abbrev eC := ![1, 31, 81]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 82 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB82I0
  exact PB82I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB82 : PrimesBelowBoundCertificate O 82 := by
  refine primesBelowBoundCertificate_of_Interval O eC 81 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 81 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 81 hC

lemma cert_eq_𝔭 : PB82.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 81 rfl rfl hel hC
