import IdealArithmetic.Examples.NF3_1_36579_1.PrimesBelow3_1_36579_1F0
import IdealArithmetic.Examples.NF3_1_36579_1.PrimesBelow3_1_36579_1F1

noncomputable section
abbrev eC := ![1, 31, 54]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 55 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB55I0
  exact PB55I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB55 : PrimesBelowBoundCertificate O 55 := by
  refine primesBelowBoundCertificate_of_Interval O eC 54 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 54 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 54 hC

lemma cert_eq_𝔭 : PB55.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 54 rfl rfl hel hC
