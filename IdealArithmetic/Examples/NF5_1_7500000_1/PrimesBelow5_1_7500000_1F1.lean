
import IdealArithmetic.Examples.NF5_1_7500000_1.RI5_1_7500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [19, 19, 7, 4, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 18, 24, 21, 7], [9, 2, 5, 23, 1], [3, 24, 4, 25, 18], [26, 13, 25, 18, 3], [0, 1]]
 g := ![![[2, 9, 24, 7, 23], [24, 6, 13, 20], [25, 0, 1], []], ![[16, 17, 27, 12, 13, 20, 11, 6], [0, 4], [28, 11, 21, 19, 16, 26, 12, 6], [17, 26, 18, 6, 27, 20, 13, 24]], ![[24, 15, 12, 18, 14, 22, 27, 9], [5, 13, 2, 16], [12, 0, 17, 2, 24, 5, 20, 5], [21, 20, 2, 27, 23, 3, 11, 1]], ![[24, 24, 20, 10, 7, 27, 15, 10], [13, 6, 16, 20], [3, 13, 4, 18, 19, 20, 24, 2], [23, 25, 13, 5, 5, 13, 27, 3]], ![[22, 16, 23, 6, 8, 0, 2, 15], [28, 5, 23, 5], [0, 9, 18, 14, 3, 24, 25, 27], [21, 18, 1, 27, 28, 3, 22, 27]]]
 h' := ![![[20, 18, 24, 21, 7], [13, 20, 3, 2, 9], [18, 18, 9, 26, 22], [0, 0, 0, 1], [0, 1]], ![[9, 2, 5, 23, 1], [7, 5, 4, 25, 11], [23, 15, 0, 27], [21, 19, 15, 9, 11], [20, 18, 24, 21, 7]], ![[3, 24, 4, 25, 18], [15, 6, 4, 1, 26], [20, 0, 11, 7, 25], [11, 26, 4, 26, 11], [9, 2, 5, 23, 1]], ![[26, 13, 25, 18, 3], [8, 6, 16, 19, 23], [20, 7, 9, 3, 22], [25, 26, 1, 16, 10], [3, 24, 4, 25, 18]], ![[0, 1], [24, 21, 2, 11, 18], [18, 18, 0, 24, 18], [9, 16, 9, 6, 26], [26, 13, 25, 18, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 6, 27, 5], [], [], []]
 b := ![[], [16, 1, 24, 19, 20], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [19, 19, 7, 4, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3291415175, 2521725885, -494342091, -3156751819, 182309167]
  a := ![0, -2, 2, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![113497075, 86956065, -17046279, -108853511, 6286523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -30, 12, -8, 10]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-43, -30, 12, -8, 10]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![23, 15, 13, 1, 0], ![11, 9, 24, 0, 1]] where
  M :=![![![-43, -30, 12, -8, 10], ![40, 9, -22, 4, -16], ![-64, -46, 5, -12, 8], ![-4, -18, -6, -5, -4], ![-40, -36, -4, -8, -1]]]
  hmulB := by decide  
  f := ![![![3, 2, 0, 0, -2]], ![![-8, -5, 2, 4, 0]], ![![0, -6, -9, 4, 8]], ![![-1, -3, -3, 3, 2]], ![![-1, -5, -6, 4, 5]]]
  g := ![![![1, 0, -4, -8, 10], ![4, 3, 10, 4, -16], ![4, 2, -1, -12, 8], ![5, 3, 5, -5, -4], ![5, 3, 4, -8, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [13, 3, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 22, 30], [24, 8, 1], [0, 1]]
 g := ![![[6, 2, 7], [24, 15, 5], [4, 30, 2], [1]], ![[11, 19, 16, 30], [29, 12, 15, 30], [12, 28, 6, 6], [26, 21, 27, 30]], ![[14, 16, 13, 19], [18, 8, 9, 18], [23, 26, 5, 14], [18, 21, 1, 1]]]
 h' := ![![[15, 22, 30], [29, 19, 10], [10, 15, 25], [18, 28, 8], [0, 1]], ![[24, 8, 1], [21, 1, 30], [14, 16, 30], [30, 22, 5], [15, 22, 30]], ![[0, 1], [25, 11, 22], [26, 0, 7], [12, 12, 18], [24, 8, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 15], []]
 b := ![[], [21, 23, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [13, 3, 23, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17273324, -12258586, 6253000, 13011328, -6455127]
  a := ![3, -65, -1, -66, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7920241, -4817173, -257136, 13011328, -6455127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 2, 0, 0, -2]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![3, 2, 0, 0, -2]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![1, 5, 1, 0, 0], ![13, 4, 0, 1, 0], ![14, 30, 0, 0, 1]] where
  M :=![![![3, 2, 0, 0, -2], ![-8, -5, 2, 4, 0], ![0, -6, -9, 4, 8], ![20, 14, -6, -19, 4], ![8, 12, 12, -8, -15]]]
  hmulB := by decide  
  f := ![![![-43, -30, 12, -8, 10]], ![![40, 9, -22, 4, -16]], ![![3, -1, -3, 0, -2]], ![![-13, -12, 2, -3, 2]], ![![18, -6, -16, 0, -11]]]
  g := ![![![1, 2, 0, 0, -2], ![-2, -1, 2, 4, 0], ![-5, -7, -9, 4, 8], ![7, 0, -6, -19, 4], ![10, 14, 12, -8, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [8, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 30], [0, 1]]
 g := ![![[9, 4], [13, 1], [16, 1], [21, 1]], ![[0, 27], [3, 30], [6, 30], [11, 30]]]
 h' := ![![[21, 30], [20, 2], [27, 1], [18, 30], [0, 1]], ![[0, 1], [0, 29], [17, 30], [28, 1], [21, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [19, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [8, 10, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-333, -242, 98, 392, 37]
  a := ![1, -4, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-195, -110, 98, 392, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-43, -30, 12, -8, 10]] ![![3, 2, 0, 0, -2]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 44, 18, 10, 10]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![21, 44, 18, 10, 10]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![19, 30, 19, 1, 0], ![9, 4, 5, 0, 1]] where
  M :=![![![21, 44, 18, 10, 10], ![40, 79, 34, 16, 20], ![80, 154, 63, 28, 32], ![44, 96, 46, 23, 18], ![76, 158, 68, 42, 39]]]
  hmulB := by decide  
  f := ![![![-31, -4, 6, -2, 6]], ![![24, -1, -2, 0, -4]], ![![-16, 6, -1, 4, 0]], ![![-5, 0, 1, 1, 0]], ![![-7, 0, 1, 0, 1]]]
  g := ![![![-7, -8, -6, 10, 10], ![-12, -13, -10, 16, 20], ![-20, -22, -17, 28, 32], ![-15, -18, -13, 23, 18], ![-29, -34, -25, 42, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [30, 22, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 8, 25], [4, 28, 12], [0, 1]]
 g := ![![[18, 16, 9], [18, 26], [28, 7, 36], [19, 1], []], ![[4, 5, 12, 7], [19, 28], [19, 36, 17, 12], [5, 7], [28, 33]], ![[7, 12, 23, 16], [15, 7], [6, 3], [21, 27], [4, 33]]]
 h' := ![![[15, 8, 25], [25, 32, 34], [11, 28, 10], [22, 33, 6], [0, 0, 1], [0, 1]], ![[4, 28, 12], [19, 25, 13], [16, 32, 18], [9, 23, 31], [14, 3, 28], [15, 8, 25]], ![[0, 1], [21, 17, 27], [8, 14, 9], [11, 18], [7, 34, 8], [4, 28, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 11], []]
 b := ![[], [13, 0, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [30, 22, 18, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-819641, -249912, 648907, 956127, -393703]
  a := ![1, 18, -3, 17, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-417371, -739430, -420243, 956127, -393703]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -1, -3, 0, -2]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![3, -1, -3, 0, -2]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![3, -1, -3, 0, -2], ![-8, -8, -1, -2, 0], ![0, -9, -6, -2, -4], ![-4, -7, -3, -1, -2], ![-4, -12, -6, -2, -3]]]
  hmulB := by decide  
  f := ![![![-25, -15, 9, -8, 10]], ![![-5, -3, 2, -2, 2]], ![![-22, -13, 8, -6, 8]], ![![-19, -12, 6, -5, 8]], ![![-15, -9, 5, -6, 7]]]
  g := ![![![4, -1, -3, 0, -2], ![4, -8, -1, -2, 0], ![11, -9, -6, -2, -4], ![6, -7, -3, -1, -2], ![11, -12, -6, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, 84, 34, 18, 18]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![45, 84, 34, 18, 18]] 
 ![![37, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![45, 84, 34, 18, 18], ![72, 151, 66, 32, 36], ![144, 282, 119, 60, 64], ![92, 184, 78, 39, 42], ![156, 310, 132, 66, 71]]]
  hmulB := by decide  
  f := ![![![-23, -12, 22, -10, -2]], ![![-17, -9, 16, -6, -2]], ![![-9, -6, 5, -2, 2]], ![![-9, -4, 12, -11, 0]], ![![-16, -6, 20, -10, -5]]]
  g := ![![![-95, 84, 34, 18, 18], ![-175, 151, 66, 32, 36], ![-323, 282, 119, 60, 64], ![-211, 184, 78, 39, 42], ![-356, 310, 132, 66, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![21, 44, 18, 10, 10]] ![![3, -1, -3, 0, -2]]
  ![![-369, -725, -305, -154, -164]] where
 M := ![![![-369, -725, -305, -154, -164]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-369, -725, -305, -154, -164]] ![![45, 84, 34, 18, 18]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-152477, -305657, -130351, -64972, -70374]]]
 hmul := by decide  
 g := ![![![![-4121, -8261, -3523, -1756, -1902]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -5, -6, -13, -1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![3, -5, -6, -13, -1]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![38, 5, 6, 13, 1]] where
  M :=![![![3, -5, -6, -13, -1], ![-4, -7, 8, -10, -26], ![-104, -100, 3, 68, -20], ![-38, -87, -88, 28, 81], ![110, 49, -56, -135, 18]]]
  hmulB := by decide  
  f := ![![![59, 23, -18, 7, -15]], ![![-60, -19, 16, -6, 14]], ![![56, 12, -13, 4, -12]], ![![6, 7, -4, 2, -3]], ![![58, 23, -18, 7, -15]]]
  g := ![![![1, 0, 0, 0, -1], ![24, 3, 4, 8, -26], ![16, 0, 3, 8, -20], ![-76, -12, -14, -25, 81], ![-14, -1, -4, -9, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [15, 2, 24, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 13, 8, 28], [38, 15, 6, 4], [16, 12, 27, 9], [0, 1]]
 g := ![![[21, 4, 27, 37], [15, 7, 40], [11, 12, 16], [26, 1], []], ![[35, 31, 3, 2, 37, 6], [19, 2, 5], [6, 11, 37], [28, 29, 22, 39, 3, 35], [38, 4, 5]], ![[39, 37, 1, 22, 33, 21], [38, 7, 25], [18, 4, 9], [18, 22, 31, 5, 18, 32], [28, 13, 16]], ![[13, 28, 25, 39, 40, 33], [14, 36, 40], [7, 0, 33], [7, 38, 0, 19, 20, 33], [14, 9, 40]]]
 h' := ![![[13, 13, 8, 28], [19, 6, 18, 23], [30, 29, 36, 9], [20, 15, 30, 37], [0, 0, 1], [0, 1]], ![[38, 15, 6, 4], [23, 8, 24, 3], [29, 31, 27, 28], [18, 24, 23, 23], [9, 38, 38, 14], [13, 13, 8, 28]], ![[16, 12, 27, 9], [27, 21, 28, 35], [8, 28, 11, 36], [14, 22, 30, 3], [40, 28, 30, 7], [38, 15, 6, 4]], ![[0, 1], [36, 6, 12, 21], [0, 35, 8, 9], [8, 21, 40, 19], [5, 16, 13, 20], [16, 12, 27, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 14, 31], []]
 b := ![[], [], [11, 29, 20, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [15, 2, 24, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![122774763, -45073720, -289720220, -87180820, 304507500]
  a := ![-1, 2, 5, 4, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-279231957, -38234420, -51628420, -98677520, 304507500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 23, -18, 7, -15]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![59, 23, -18, 7, -15]] 
 ![![41, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![59, 23, -18, 7, -15], ![-60, -19, 16, -6, 14], ![56, 12, -13, 4, -12], ![6, 7, -4, 2, -3], ![22, 1, -4, 1, -4]]]
  hmulB := by decide  
  f := ![![![3, -5, -6, -13, -1]], ![![1, -2, -2, -5, -1]], ![![-1, -5, -3, -5, -1]], ![![2, -7, -8, -12, 1]], ![![4, -1, -4, -9, 0]]]
  g := ![![![2, 23, -18, 7, -15], ![-3, -19, 16, -6, 14], ![5, 12, -13, 4, -12], ![-1, 7, -4, 2, -3], ![3, 1, -4, 1, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![3, -5, -6, -13, -1]] ![![59, 23, -18, 7, -15]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1983, 932, -643, 273, -525]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![1983, 932, -643, 273, -525]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![28, 31, 19, 1, 0], ![27, 15, 41, 0, 1]] where
  M :=![![![1983, 932, -643, 273, -525], ![-2100, -760, 659, -236, 546], ![2184, 743, -524, 226, -472], ![106, 266, -71, 66, -47], ![998, 295, -162, 89, -170]]]
  hmulB := by decide  
  f := ![![![109, 106, 27, -109, -41]], ![![-164, -28, 215, 136, -218]], ![![-872, -821, -164, 866, 272]], ![![-418, -313, 78, 398, -41]], ![![-785, -694, -60, 770, 149]]]
  g := ![![![198, 8, 365, 273, -525], ![-238, -38, -401, -236, 546], ![200, 19, 338, 226, -472], ![-11, -25, 14, 66, -47], ![72, 2, 119, 89, -170]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [6, 38, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 13, 3], [6, 29, 40], [0, 1]]
 g := ![![[16, 28, 14], [2, 32, 4], [18, 17], [21, 39, 1], []], ![[19, 39, 1, 18], [19, 0, 19, 20], [13, 21], [22, 35, 31, 29], [42, 9]], ![[40, 28, 5, 16], [40, 26, 7, 1], [33, 35], [38, 35, 21, 9], [5, 9]]]
 h' := ![![[33, 13, 3], [31, 30, 10], [30, 31, 41], [3, 0, 19], [0, 0, 1], [0, 1]], ![[6, 29, 40], [17, 38, 36], [24, 9, 35], [39, 2, 35], [20, 25, 29], [33, 13, 3]], ![[0, 1], [13, 18, 40], [32, 3, 10], [31, 41, 32], [6, 18, 13], [6, 29, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 21], []]
 b := ![[], [26, 7, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [6, 38, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![371366, 650612, 652628, -447000, -754156]
  a := ![0, -10, -2, -20, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![773246, 600464, 931768, -447000, -754156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, -106, -27, 109, 41]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-109, -106, -27, 109, 41]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![12, 5, 1, 0, 0], ![13, 37, 0, 1, 0], ![42, 24, 0, 0, 1]] where
  M :=![![![-109, -106, -27, 109, 41], ![164, 28, -215, -136, 218], ![872, 821, 164, -866, -272], ![-626, -40, 951, 504, -975], ![-1514, -1377, -190, 1493, 368]]]
  hmulB := by decide  
  f := ![![![-1983, -932, 643, -273, 525]], ![![2100, 760, -659, 236, -546]], ![![-360, -189, 115, -54, 94]], ![![1205, 366, -371, 119, -310]], ![![-788, -493, 264, -137, 212]]]
  g := ![![![-68, -116, -27, 109, 41], ![-108, 21, -215, -136, 218], ![502, 897, 164, -866, -272], ![520, -1, 951, 504, -975], ![-793, -1500, -190, 1493, 368]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [3, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 42], [0, 1]]
 g := ![![[31, 14], [0, 21], [38], [0, 6], [1]], ![[19, 29], [25, 22], [38], [1, 37], [1]]]
 h' := ![![[36, 42], [0, 33], [15, 35], [0, 34], [40, 36], [0, 1]], ![[0, 1], [27, 10], [28, 8], [20, 9], [3, 7], [36, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [37, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [3, 7, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![627, -660, -2007, 105, 2067]
  a := ![13, 0, 4, 1, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1476, -1026, -2007, 105, 2067]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![1983, 932, -643, 273, -525]] ![![-109, -106, -27, 109, 41]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93, 486, 158, 104, 94]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![93, 486, 158, 104, 94]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![28, 40, 1, 0, 0], ![4, 37, 0, 1, 0], ![13, 34, 0, 0, 1]] where
  M :=![![![93, 486, 158, 104, 94], ![376, 627, 382, 128, 208], ![832, 1590, 499, 348, 256], ![324, 864, 430, 179, 244], ![904, 1660, 592, 360, 307]]]
  hmulB := by decide  
  f := ![![![-165, 86, 438, 112, -462]], ![![-1848, -1575, -26, 1800, 224]], ![![-1652, -1310, 167, 1588, -8]], ![![-1296, -1089, 12, 1259, 124]], ![![-1399, -1068, 222, 1336, -95]]]
  g := ![![![-127, -274, 158, 104, 94], ![-288, -563, 382, 128, 208], ![-380, -850, 499, 348, 256], ![-332, -665, 430, 179, 244], ![-449, -974, 592, 360, 307]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [33, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 46], [0, 1]]
 g := ![![[33, 21], [7, 7], [34, 12], [16, 17], [1]], ![[6, 26], [45, 40], [32, 35], [21, 30], [1]]]
 h' := ![![[39, 46], [4, 31], [6, 17], [36, 24], [14, 39], [0, 1]], ![[0, 1], [38, 16], [11, 30], [32, 23], [31, 8], [39, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [25, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [33, 8, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![446, 254, -166, -494, 204]
  a := ![-1, -4, -1, -5, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![94, 388, -166, -494, 204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -14, -1, 13, 1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-15, -14, -1, 13, 1]] 
 ![![47, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-15, -14, -1, 13, 1], ![4, -12, -27, -4, 26], ![104, 81, -8, -106, -8], ![-18, 38, 107, 2, -119], ![-186, -153, 14, 173, -2]]]
  hmulB := by decide  
  f := ![![![9679, 3976, -3019, 1195, -2499]], ![![817, 352, -262, 105, -215]], ![![4734, 1911, -1462, 576, -1214]], ![![2695, 1124, -848, 337, -700]], ![![496, 179, -144, 55, -122]]]
  g := ![![![-2, -14, -1, 13, 1], ![14, -12, -27, -4, 26], ![27, 81, -8, -106, -8], ![-50, 38, 107, 2, -119], ![-42, -153, 14, 173, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 312, 73, 71, 27]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![271, 312, 73, 71, 27]] 
 ![![47, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![271, 312, 73, 71, 27], ![108, 452, 241, 92, 142], ![568, 917, 360, 198, 184], ![314, 606, 239, 130, 127], ![538, 989, 418, 211, 222]]]
  hmulB := by decide  
  f := ![![![-767, -910, -509, 801, 639]], ![![-272, -360, -253, 292, 306]], ![![-239, -291, -173, 251, 215]], ![![-908, -916, -289, 914, 413]], ![![-868, -1003, -524, 901, 666]]]
  g := ![![![-248, 312, 73, 71, 27], ![-505, 452, 241, 92, 142], ![-880, 917, 360, 198, 184], ![-587, 606, 239, 130, 127], ![-982, 989, 418, 211, 222]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -21, -13, 18, 16]] i)))

def SI47N3: IdealEqSpanCertificate' Table ![![-17, -21, -13, 18, 16]] 
 ![![47, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-17, -21, -13, 18, 16], ![64, 34, -39, -58, 36], ![144, 169, 92, -150, -116], ![-264, -131, 179, 237, -168], ![-264, -294, -138, 272, 179]]]
  hmulB := by decide  
  f := ![![![-1151, -125, 349, -62, 296]], ![![-685, -69, 214, -36, 180]], ![![-133, 0, 43, -4, 36]], ![![-175, -16, 58, -9, 48]], ![![-1026, -96, 316, -52, 267]]]
  g := ![![![-3, -21, -13, 18, 16], ![-39, 34, -39, -58, 36], ![15, 169, 92, -150, -116], ![171, -131, 179, 237, -168], ![-10, -294, -138, 272, 179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N3 : Nat.card (O ⧸ I47N3) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N3)

lemma isPrimeI47N3 : Ideal.IsPrime I47N3 := prime_ideal_of_norm_prime hp47.out _ NI47N3
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![93, 486, 158, 104, 94]] ![![-15, -14, -1, 13, 1]]
  ![![-2375, -4766, -2035, -1013, -1099]] where
 M := ![![![-2375, -4766, -2035, -1013, -1099]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-2375, -4766, -2035, -1013, -1099]] ![![271, 312, 73, 71, 27]]
  ![![-3223577, -6462116, -2756070, -1373606, -1487966]] where
 M := ![![![-3223577, -6462116, -2756070, -1373606, -1487966]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N2 : IdealMulLeCertificate' Table 
  ![![-3223577, -6462116, -2756070, -1373606, -1487966]] ![![-17, -21, -13, 18, 16]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-193687, -388267, -165581, -82532, -89394]]]
 hmul := by decide  
 g := ![![![![-4121, -8261, -3523, -1756, -1902]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2, I47N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
    exact isPrimeI47N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1 ⊙ MulI47N2)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -19, -46, -3, 49]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![7, -19, -46, -3, 49]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![38, 18, 38, 14, 1]] where
  M :=![![![7, -19, -46, -3, 49], ![196, 157, -16, -190, -6], ![-24, 156, 347, -20, -380], ![-858, -677, 96, 822, -17], ![-46, -337, -576, 103, 632]]]
  hmulB := by decide  
  f := ![![![83, 13, -18, 5, -17]], ![![-68, -3, 8, -2, 10]], ![![40, -20, -1, -4, -4]], ![![26, 13, -12, 4, -9]], ![![72, -3, -14, 1, -14]]]
  g := ![![![-35, -17, -36, -13, 49], ![8, 5, 4, -2, -6], ![272, 132, 279, 100, -380], ![-4, -7, 14, 20, -17], ![-454, -221, -464, -165, 632]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [20, 26, 52, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 27, 40, 27], [24, 37, 1, 43], [14, 41, 12, 36], [0, 1]]
 g := ![![[13, 40, 12, 16], [46, 51, 36], [3, 17, 9, 37], [48, 43, 1], []], ![[7, 52, 17, 10, 8, 33], [42, 45, 28], [4, 46, 27, 19, 51, 45], [36, 11, 13], [31, 23, 16, 46, 42, 20]], ![[16, 48, 45, 33, 26, 42], [51, 18, 52], [40, 3, 40, 27, 36, 42], [22, 0, 40], [17, 35, 45, 32, 18, 7]], ![[44, 29, 30, 14, 15, 38], [8, 25, 11], [0, 17, 10, 5, 18, 15], [9, 22, 47], [2, 0, 8, 32, 15, 16]]]
 h' := ![![[5, 27, 40, 27], [30, 5, 5, 49], [46, 42, 32, 47], [47, 12, 23, 14], [0, 0, 0, 1], [0, 1]], ![[24, 37, 1, 43], [1, 49, 51, 38], [24, 37, 32, 44], [28, 34, 2, 14], [35, 17, 10, 15], [5, 27, 40, 27]], ![[14, 41, 12, 36], [47, 47, 41, 21], [31, 10, 14, 23], [44, 4, 36, 32], [22, 42, 29, 27], [24, 37, 1, 43]], ![[0, 1], [5, 5, 9, 51], [35, 17, 28, 45], [33, 3, 45, 46], [1, 47, 14, 10], [14, 41, 12, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 33, 36], []]
 b := ![[], [], [29, 34, 28, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [20, 26, 52, 10, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8429829, 11741066, 8946314, -9251946, -10652913]
  a := ![3, -4, 0, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7796991, 3839500, 7806736, 2639412, -10652913]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 13, -18, 5, -17]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![83, 13, -18, 5, -17]] 
 ![![53, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![83, 13, -18, 5, -17], ![-68, -3, 8, -2, 10], ![40, -20, -1, -4, -4], ![26, 13, -12, 4, -9], ![2, -21, 4, -5, 2]]]
  hmulB := by decide  
  f := ![![![7, -19, -46, -3, 49]], ![![7, -6, -22, -5, 23]], ![![1, -1, -3, -1, 3]], ![![-15, -16, -6, 15, 8]], ![![6, -25, -56, -1, 60]]]
  g := ![![![15, 13, -18, 5, -17], ![-11, -3, 8, -2, 10], ![15, -20, -1, -4, -4], ![5, 13, -12, 4, -9], ![8, -21, 4, -5, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![7, -19, -46, -3, 49]] ![![83, 13, -18, 5, -17]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -40, 15, -13, 21]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-27, -40, 15, -13, 21]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![24, 29, 26, 5, 1]] where
  M :=![![![-27, -40, 15, -13, 21], ![84, 72, -27, -12, -26], ![-104, -47, 84, -2, -24], ![-90, -94, -9, 114, 11], ![-30, -51, -62, -21, 102]]]
  hmulB := by decide  
  f := ![![![23, 42, 17, 9, 9]], ![![36, 76, 33, 16, 18]], ![![72, 141, 60, 30, 32]], ![![46, 92, 39, 20, 21]], ![![64, 127, 54, 27, 29]]]
  g := ![![![-9, -11, -9, -2, 21], ![12, 14, 11, 2, -26], ![8, 11, 12, 2, -24], ![-6, -7, -5, 1, 11], ![-42, -51, -46, -9, 102]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [9, 6, 19, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 37, 18, 39], [47, 18, 9, 8], [8, 3, 32, 12], [0, 1]]
 g := ![![[20, 25, 17, 28], [22, 53, 4, 28], [53, 55, 48], [35, 30, 52, 1], []], ![[23, 41, 15, 5, 43, 56], [48, 20, 12, 40, 41, 34], [2, 0, 41], [5, 20, 52, 42, 35, 42], [30, 23, 11, 32, 15, 24]], ![[23, 52, 26, 47, 23, 56], [46, 11, 14, 5, 3, 23], [9, 57, 9], [18, 25, 39, 12, 53, 54], [46, 2, 47, 50, 32, 40]], ![[55, 38, 32, 46, 54, 5], [0, 5, 27, 35, 58, 26], [21, 24, 5], [20, 39, 17, 56, 44, 16], [57, 1, 53, 17, 17, 17]]]
 h' := ![![[56, 37, 18, 39], [38, 10, 43, 21], [41, 38, 16, 21], [39, 51, 44, 44], [0, 0, 0, 1], [0, 1]], ![[47, 18, 9, 8], [42, 16, 11, 3], [45, 29, 4, 55], [2, 25, 35, 10], [57, 22, 43, 13], [56, 37, 18, 39]], ![[8, 3, 32, 12], [39, 39, 33, 40], [6, 9, 28, 5], [21, 39, 39, 56], [41, 48, 1, 13], [47, 18, 9, 8]], ![[0, 1], [54, 53, 31, 54], [13, 42, 11, 37], [5, 3, 0, 8], [58, 48, 15, 32], [8, 3, 32, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 24, 13], []]
 b := ![[], [], [43, 47, 40, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [9, 6, 19, 7, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1471370, -19272728, -35204229, 5447297, 38842993]
  a := ![1, 0, -3, -1, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15825478, -19418975, -17713933, -3199452, 38842993]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -42, -17, -9, -9]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-23, -42, -17, -9, -9]] 
 ![![59, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-23, -42, -17, -9, -9], ![-36, -76, -33, -16, -18], ![-72, -141, -60, -30, -32], ![-46, -92, -39, -20, -21], ![-78, -155, -66, -33, -36]]]
  hmulB := by decide  
  f := ![![![27, 40, -15, 13, -21]], ![![21, 32, -12, 11, -17]], ![![10, 13, -6, 4, -6]], ![![18, 26, -9, 6, -13]], ![![6, 9, -2, 3, -6]]]
  g := ![![![47, -42, -17, -9, -9], ![86, -76, -33, -16, -18], ![159, -141, -60, -30, -32], ![104, -92, -39, -20, -21], ![175, -155, -66, -33, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-27, -40, 15, -13, 21]] ![![-23, -42, -17, -9, -9]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4343, 3517, -296, -4191, -135]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![4343, 3517, -296, -4191, -135]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![46, 11, 4, 8, 1]] where
  M :=![![![4343, 3517, -296, -4191, -135], ![-540, 3507, 7708, -322, -8382], ![-33528, -26360, 3829, 32180, -644], ![-1018, -17891, -33124, 4634, 36371], ![55978, 42491, -9348, -53405, 4312]]]
  hmulB := by decide  
  f := ![![![-389, -1115, -548, -231, -313]], ![![-1252, -2189, -884, -470, -462]], ![![-1848, -3984, -1719, -844, -940]], ![![-1254, -2569, -1128, -544, -613]], ![![-840, -1906, -864, -401, -478]]]
  g := ![![![173, 82, 4, -51, -135], ![6312, 1569, 676, 1094, -8382], ![-64, -316, 105, 612, -644], ![-27444, -6852, -2928, -4694, 36371], ![-2334, -81, -436, -1441, 4312]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [7, 49, 15, 45, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 28, 39, 23], [47, 13, 3, 51], [31, 19, 19, 48], [0, 1]]
 g := ![![[35, 33, 49, 57], [60, 14, 36], [24, 59, 7, 41], [29, 58, 16, 1], []], ![[13, 0, 25, 12, 12, 23], [38, 3, 9], [50, 3, 50, 17, 40, 55], [57, 28, 22, 15, 54, 37], [28, 1, 12, 48, 60, 28]], ![[30, 28, 2, 42, 49, 31], [44, 58, 42], [37, 38, 4, 43, 0, 33], [11, 3, 54, 28, 25, 43], [58, 56, 42, 46, 28, 37]], ![[25, 28, 28, 19, 7, 12], [16, 57, 19], [28, 2, 17, 1, 8, 19], [24, 10, 18, 31, 13, 20], [5, 9, 6, 52, 40, 60]]]
 h' := ![![[60, 28, 39, 23], [49, 27, 40, 22], [15, 31, 57, 55], [41, 3, 27, 23], [0, 0, 0, 1], [0, 1]], ![[47, 13, 3, 51], [44, 0, 6, 1], [35, 33, 7, 3], [15, 33, 16, 14], [47, 47, 18, 33], [60, 28, 39, 23]], ![[31, 19, 19, 48], [49, 53, 12, 8], [33, 35, 53, 46], [40, 12, 59, 36], [22, 18, 30, 21], [47, 13, 3, 51]], ![[0, 1], [44, 42, 3, 30], [20, 23, 5, 18], [26, 13, 20, 49], [49, 57, 13, 6], [31, 19, 19, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [46, 36], []]
 b := ![[], [], [36, 53, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [7, 49, 15, 45, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2609, -10852, -17222, 10208, 19698]
  a := ![4, 1, 0, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14897, -3730, -1574, -2416, 19698]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-389, -1115, -548, -231, -313]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-389, -1115, -548, -231, -313]] 
 ![![61, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-389, -1115, -548, -231, -313], ![-1252, -2189, -884, -470, -462], ![-1848, -3984, -1719, -844, -940], ![-1254, -2569, -1128, -544, -613], ![-2150, -4409, -1872, -937, -1014]]]
  hmulB := by decide  
  f := ![![![4343, 3517, -296, -4191, -135]], ![![3195, 2652, -92, -3097, -237]], ![![2939, 2393, -175, -2839, -119]], ![![2404, 1667, -708, -2260, 521]], ![![2484, 1965, -260, -2387, 22]]]
  g := ![![![1498, -1115, -548, -231, -313], ![2733, -2189, -884, -470, -462], ![5099, -3984, -1719, -844, -940], ![3305, -2569, -1128, -544, -613], ![5609, -4409, -1872, -937, -1014]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![4343, 3517, -296, -4191, -135]] ![![-389, -1115, -548, -231, -313]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB171I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB171I1 : PrimesBelowBoundCertificateInterval O 23 61 171 where
  m := 9
  g := ![1, 2, 3, 2, 2, 4, 2, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB171I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2, I47N3]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20511149]
    · exact ![29791, 961]
    · exact ![50653, 37, 37]
    · exact ![2825761, 41]
    · exact ![79507, 1849]
    · exact ![2209, 47, 47, 47]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
      exact NI47N3
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I37N1, I37N2, I41N1, I47N1, I47N2, I47N3, I53N1, I59N1, I61N1]
  Il := ![[], [], [I37N1, I37N2], [I41N1], [], [I47N1, I47N2, I47N3], [I53N1], [I59N1], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
