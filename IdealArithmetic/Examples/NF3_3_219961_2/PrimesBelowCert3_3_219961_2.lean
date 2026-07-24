import IdealArithmetic.Examples.NF3_3_219961_2.PrimesBelow3_3_219961_2F0
import IdealArithmetic.Examples.NF3_3_219961_2.PrimesBelow3_3_219961_2F1
import IdealArithmetic.Examples.NF3_3_219961_2.PrimesBelow3_3_219961_2F2

noncomputable section
abbrev eC := ![1, 31, 79, 104]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 105 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB105I0
  exact PB105I1
  exact PB105I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB105 : PrimesBelowBoundCertificate O 105 := by
  refine primesBelowBoundCertificate_of_Interval O eC 104 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 104 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 104 hC

lemma cert_eq_𝔭 : PB105.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 104 rfl rfl hel hC
