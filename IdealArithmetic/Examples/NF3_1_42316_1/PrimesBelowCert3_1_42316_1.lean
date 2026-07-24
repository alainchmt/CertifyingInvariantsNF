import IdealArithmetic.Examples.NF3_1_42316_1.PrimesBelow3_1_42316_1F0
import IdealArithmetic.Examples.NF3_1_42316_1.PrimesBelow3_1_42316_1F1

noncomputable section
abbrev eC := ![1, 31, 58]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 59 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB59I0
  exact PB59I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB59 : PrimesBelowBoundCertificate O 59 := by
  refine primesBelowBoundCertificate_of_Interval O eC 58 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 58 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 58 hC

lemma cert_eq_𝔭 : PB59.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 58 rfl rfl hel hC
