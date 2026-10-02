import IdealArithmetic.MordellExamples.MordellExample142.NF2_2_568_1.PrimesBelow2_2_568_1F0

namespace NF2_2_568_1

noncomputable section
abbrev eC := ![1, 11]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 12 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB12I0

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB12 : PrimesBelowBoundCertificate O 12 := by
  refine primesBelowBoundCertificate_of_Interval O eC 11 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 11 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 11 hC

lemma cert_eq_𝔭 : PB12.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 11 rfl rfl hel hC

end

end NF2_2_568_1
