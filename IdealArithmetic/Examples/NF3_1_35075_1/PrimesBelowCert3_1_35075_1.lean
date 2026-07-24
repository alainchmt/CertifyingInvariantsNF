import IdealArithmetic.Examples.NF3_1_35075_1.PrimesBelow3_1_35075_1F0
import IdealArithmetic.Examples.NF3_1_35075_1.PrimesBelow3_1_35075_1F1

noncomputable section
abbrev eC := ![1, 31, 53]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 54 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB54I0
  exact PB54I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB54 : PrimesBelowBoundCertificate O 54 := by
  refine primesBelowBoundCertificate_of_Interval O eC 53 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 53 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 53 hC

lemma cert_eq_𝔭 : PB54.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 53 rfl rfl hel hC
