import IdealArithmetic.Examples.NF3_3_582169_2.PrimesBelow3_3_582169_2F0
import IdealArithmetic.Examples.NF3_3_582169_2.PrimesBelow3_3_582169_2F1
import IdealArithmetic.Examples.NF3_3_582169_2.PrimesBelow3_3_582169_2F2
import IdealArithmetic.Examples.NF3_3_582169_2.PrimesBelow3_3_582169_2F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 169]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 170 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB170I0
  exact PB170I1
  exact PB170I2
  exact PB170I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB170 : PrimesBelowBoundCertificate O 170 := by
  refine primesBelowBoundCertificate_of_Interval O eC 169 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 169 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 169 hC

lemma cert_eq_𝔭 : PB170.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 169 rfl rfl hel hC
