import IdealArithmetic.Examples.NF3_1_508248_2.PrimesBelow3_1_508248_2F0
import IdealArithmetic.Examples.NF3_1_508248_2.PrimesBelow3_1_508248_2F1
import IdealArithmetic.Examples.NF3_1_508248_2.PrimesBelow3_1_508248_2F2
import IdealArithmetic.Examples.NF3_1_508248_2.PrimesBelow3_1_508248_2F3
import IdealArithmetic.Examples.NF3_1_508248_2.PrimesBelow3_1_508248_2F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 201]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 202 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB202I0
  exact PB202I1
  exact PB202I2
  exact PB202I3
  exact PB202I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB202 : PrimesBelowBoundCertificate O 202 := by
  refine primesBelowBoundCertificate_of_Interval O eC 201 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 201 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 201 hC

lemma cert_eq_𝔭 : PB202.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 201 rfl rfl hel hC
