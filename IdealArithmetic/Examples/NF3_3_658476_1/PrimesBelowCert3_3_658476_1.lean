import IdealArithmetic.Examples.NF3_3_658476_1.PrimesBelow3_3_658476_1F0
import IdealArithmetic.Examples.NF3_3_658476_1.PrimesBelow3_3_658476_1F1
import IdealArithmetic.Examples.NF3_3_658476_1.PrimesBelow3_3_658476_1F2
import IdealArithmetic.Examples.NF3_3_658476_1.PrimesBelow3_3_658476_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 180]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 181 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB181I0
  exact PB181I1
  exact PB181I2
  exact PB181I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB181 : PrimesBelowBoundCertificate O 181 := by
  refine primesBelowBoundCertificate_of_Interval O eC 180 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 180 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 180 hC

lemma cert_eq_𝔭 : PB181.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 180 rfl rfl hel hC
