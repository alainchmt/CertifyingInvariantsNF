
import IdealArithmetic.Examples.NF3_1_936684_4.RI3_1_936684_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [72, 12, 168, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 167, 77], [14, 29, 120], [0, 1]]
 g := ![![[8, 35, 160], [58, 164], [79, 93, 175], [130, 160], [33, 47], [53, 53], [1]], ![[154, 97, 73, 151], [43, 191], [177, 17, 61, 151], [24, 187], [139, 109], [16, 191], [11, 84, 135, 84]], ![[173, 53, 18, 123], [107, 160], [31, 194, 36, 14], [58, 15], [89, 154], [75, 158], [195, 149, 5, 113]]]
 h' := ![![[15, 167, 77], [192, 102, 102], [25, 63, 19], [157, 182, 61], [109, 3, 102], [186, 34, 21], [125, 185, 29], [0, 1]], ![[14, 29, 120], [50, 133, 174], [83, 190, 83], [60, 67, 23], [58, 148, 37], [120, 14, 75], [22, 165, 114], [15, 167, 77]], ![[0, 1], [143, 159, 118], [178, 141, 95], [12, 145, 113], [53, 46, 58], [74, 149, 101], [130, 44, 54], [14, 29, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170, 186], []]
 b := ![[], [64, 141, 169], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [72, 12, 168, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-93378, 5910, 5910]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-474, 30, 30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![98, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![98, 1, 0]] 
 ![![199, 0, 0], ![98, 1, 0], ![147, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![98, 1, 0], ![0, 98, 1], ![350, 84, 98]]]
  hmulB := by decide  
  f := ![![![6077, 62, 0], ![-12338, 0, 0]], ![![2842, 29, 0], ![-5770, 0, 0]], ![![4361, 44, 0], ![-8854, 1, 0]]]
  g := ![![![1, 0, 0], ![-98, 199, 0], ![-147, 0, 199]], ![![0, 1, 0], ![-49, 98, 1], ![-112, 84, 98]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-78, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-78, 1, 0]] 
 ![![199, 0, 0], ![121, 1, 0], ![85, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-78, 1, 0], ![0, -78, 1], ![350, 84, -78]]]
  hmulB := by decide  
  f := ![![![8269, -106, 0], ![21094, 0, 0]], ![![5071, -65, 0], ![12936, 0, 0]], ![![3619, -46, 0], ![9232, 1, 0]]]
  g := ![![![1, 0, 0], ![-121, 199, 0], ![-85, 0, 199]], ![![-1, 1, 0], ![47, -78, 1], ![-16, 84, -78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-20, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-20, 1, 0]] 
 ![![199, 0, 0], ![179, 1, 0], ![197, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-20, 1, 0], ![0, -20, 1], ![350, 84, -20]]]
  hmulB := by decide  
  f := ![![![241, -12, 0], ![2388, 0, 0]], ![![221, -11, 0], ![2190, 0, 0]], ![![243, -12, 0], ![2408, 1, 0]]]
  g := ![![![1, 0, 0], ![-179, 199, 0], ![-197, 0, 199]], ![![-1, 1, 0], ![17, -20, 1], ![-54, 84, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![98, 1, 0]] ![![199, 0, 0], ![-78, 1, 0]]
  ![![199, 0, 0], ![-82, 20, 1]] where
 M := ![![![39601, 0, 0], ![-15522, 199, 0]], ![![19502, 199, 0], ![-7644, 20, 1]]]
 hmul := by decide  
 g := ![![![![199, 0, 0], ![0, 0, 0]], ![![4, -19, -1], ![199, 0, 0]]], ![![![98, 1, 0], ![0, 0, 0]], ![![44, -20, -1], ![200, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-82, 20, 1]] ![![199, 0, 0], ![-20, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-3980, 199, 0]], ![![-16318, 3980, 199], ![1990, -398, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-20, 1, 0]]], ![![![-82, 20, 1]], ![![10, -2, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![15, -47, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![15, -47, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![15, 164, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![15, -47, 1], ![350, 99, -47], ![-16450, -3598, 99]]]
  hmulB := by decide  
  f := ![![![-14, 47, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -164, 211]], ![![0, -1, 1], ![5, 37, -47], ![-85, -94, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [64, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 210], [0, 1]]
 g := ![![[173, 122], [163, 143], [182], [126], [57, 65], [150], [111, 1]], ![[0, 89], [0, 68], [182], [126], [98, 146], [150], [11, 210]]]
 h' := ![![[111, 210], [118, 132], [105, 96], [88, 56], [150, 45], [153, 109], [70, 19], [0, 1]], ![[0, 1], [0, 79], [0, 115], [185, 155], [81, 166], [14, 102], [69, 192], [111, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [64, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [64, 100, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4235, 1946, 1054]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-95, -810, 1054]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![47, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![47, 1, 0]] 
 ![![211, 0, 0], ![47, 1, 0], ![112, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![47, 1, 0], ![0, 47, 1], ![350, 84, 47]]]
  hmulB := by decide  
  f := ![![![330, 7, 0], ![-1477, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![152, 3, 0], ![-680, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 211, 0], ![-112, 0, 211]], ![![0, 1, 0], ![-11, 47, 1], ![-42, 84, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![15, -47, 1]] ![![211, 0, 0], ![47, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![9917, 211, 0]], ![![3165, -9917, 211], ![1055, -2110, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![47, 1, 0]]], ![![![15, -47, 1]], ![![5, -10, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [41, 113, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 134, 173], [210, 88, 50], [0, 1]]
 g := ![![[139, 157, 72], [145, 192, 166], [121, 29, 130], [30, 60, 83], [120, 188, 98], [25, 37], [1]], ![[91, 22, 9, 88], [39, 13, 125, 21], [93, 107, 133, 21], [179, 114, 144, 5], [187, 186, 22, 6], [33, 153], [99, 210, 100, 103]], ![[106, 37, 26, 213], [55, 71, 61, 39], [104, 88, 88, 69], [44, 92, 210, 156], [36, 118, 128, 199], [124, 201], [217, 0, 205, 120]]]
 h' := ![![[99, 134, 173], [76, 176, 133], [168, 147, 122], [108, 144, 24], [209, 86, 200], [210, 18, 118], [182, 110, 86], [0, 1]], ![[210, 88, 50], [65, 74, 5], [123, 178, 41], [207, 69, 41], [18, 40, 143], [123, 34, 118], [204, 88, 61], [99, 134, 173]], ![[0, 1], [121, 196, 85], [55, 121, 60], [52, 10, 158], [101, 97, 103], [59, 171, 210], [56, 25, 76], [210, 88, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 183], []]
 b := ![[], [52, 164, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [41, 113, 137, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![296367, -53743, -5798]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1329, -241, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![29, 106, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![29, 106, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![29, 106, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![29, 106, 1], ![350, 113, 106], ![37100, 9254, 113]]]
  hmulB := by decide  
  f := ![![![-28, -106, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -106, 227]], ![![0, 0, 1], ![-12, -49, 106], ![149, -12, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [206, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [185, 226], [0, 1]]
 g := ![![[225, 196], [180, 210], [21], [29], [1], [21, 53], [185, 1]], ![[165, 31], [213, 17], [21], [29], [1], [65, 174], [143, 226]]]
 h' := ![![[185, 226], [148, 14], [126, 133], [162, 193], [190, 211], [214, 226], [26, 196], [0, 1]], ![[0, 1], [14, 213], [215, 94], [1, 34], [181, 16], [29, 1], [193, 31], [185, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [98, 156]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [206, 42, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1851, 2690, 625]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88, -280, 625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-106, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-106, 1, 0]] 
 ![![227, 0, 0], ![121, 1, 0], ![114, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-106, 1, 0], ![0, -106, 1], ![350, 84, -106]]]
  hmulB := by decide  
  f := ![![![2863, -27, 0], ![6129, 0, 0]], ![![1485, -14, 0], ![3179, 0, 0]], ![![1534, -14, 0], ![3284, 1, 0]]]
  g := ![![![1, 0, 0], ![-121, 227, 0], ![-114, 0, 227]], ![![-1, 1, 0], ![56, -106, 1], ![10, 84, -106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![29, 106, 1]] ![![227, 0, 0], ![-106, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-24062, 227, 0]], ![![6583, 24062, 227], ![-2724, -11123, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-106, 1, 0]]], ![![![29, 106, 1]], ![![-12, -49, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-129, -111, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-129, -111, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![100, 118, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-129, -111, 1], ![350, -45, -111], ![-38850, -8974, -45]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-100, -118, 229]], ![![-1, -1, 1], ![50, 57, -111], ![-150, -16, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [132, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [134, 228], [0, 1]]
 g := ![![[169, 144], [181], [106, 121], [158], [228], [49, 70], [134, 1]], ![[0, 85], [181], [61, 108], [158], [228], [40, 159], [39, 228]]]
 h' := ![![[134, 228], [224, 12], [206, 69], [163, 11], [62, 171], [173, 122], [174, 191], [0, 1]], ![[0, 1], [0, 217], [63, 160], [34, 218], [76, 58], [33, 107], [120, 38], [134, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [101, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [132, 95, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![832, 423, -10]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 7, -10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![111, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![111, 1, 0]] 
 ![![229, 0, 0], ![111, 1, 0], ![45, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![111, 1, 0], ![0, 111, 1], ![350, 84, 111]]]
  hmulB := by decide  
  f := ![![![7105, 64, 0], ![-14656, 0, 0]], ![![3441, 31, 0], ![-7098, 0, 0]], ![![1275, 11, 0], ![-2630, 1, 0]]]
  g := ![![![1, 0, 0], ![-111, 229, 0], ![-45, 0, 229]], ![![0, 1, 0], ![-54, 111, 1], ![-61, 84, 111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-129, -111, 1]] ![![229, 0, 0], ![111, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![25419, 229, 0]], ![![-29541, -25419, 229], ![-13969, -12366, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![111, 1, 0]]], ![![![-129, -111, 1]], ![![-61, -54, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-169, 71, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-169, 71, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![64, 71, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-169, 71, 1], ![350, -85, 71], ![24850, 6314, -85]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -71, 233]], ![![-1, 0, 1], ![-18, -22, 71], ![130, 53, -85]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [116, 162, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 232], [0, 1]]
 g := ![![[142, 231], [224], [38], [49, 159], [85], [183, 92], [71, 1]], ![[0, 2], [224], [38], [154, 74], [85], [191, 141], [142, 232]]]
 h' := ![![[71, 232], [50, 124], [95, 199], [141, 182], [85, 208], [208, 28], [152, 32], [0, 1]], ![[0, 1], [0, 109], [11, 34], [15, 51], [174, 25], [99, 205], [94, 201], [71, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [176, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [116, 162, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13579, 6658, 609]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-109, -157, 609]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-71, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-71, 1, 0]] 
 ![![233, 0, 0], ![162, 1, 0], ![85, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-71, 1, 0], ![0, -71, 1], ![350, 84, -71]]]
  hmulB := by decide  
  f := ![![![11503, -162, 0], ![37746, 0, 0]], ![![8024, -113, 0], ![26330, 0, 0]], ![![4211, -59, 0], ![13818, 1, 0]]]
  g := ![![![1, 0, 0], ![-162, 233, 0], ![-85, 0, 233]], ![![-1, 1, 0], ![49, -71, 1], ![-31, 84, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-169, 71, 1]] ![![233, 0, 0], ![-71, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-16543, 233, 0]], ![![-39377, 16543, 233], ![12349, -5126, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-71, 1, 0]]], ![![![-169, 71, 1]], ![![53, -22, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [71, 229, 171, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [202, 185, 107], [105, 53, 132], [0, 1]]
 g := ![![[152, 209, 170], [100, 24, 6], [37, 56, 150], [161, 230, 134], [122, 51], [62, 73, 83], [1]], ![[112, 225, 205, 138], [39, 5, 142, 208], [174, 51, 58, 228], [167, 56, 141, 111], [104, 98], [170, 203, 147, 82], [163, 153, 93, 168]], ![[118, 182, 115, 102], [62, 185, 45, 180], [188, 192, 190, 67], [215, 154, 11, 162], [20, 58], [216, 238, 142, 125], [238, 17, 215, 71]]]
 h' := ![![[202, 185, 107], [70, 17, 109], [2, 226, 217], [41, 232, 110], [143, 228, 143], [139, 0, 23], [168, 10, 68], [0, 1]], ![[105, 53, 132], [119, 90, 187], [94, 185, 72], [94, 95, 62], [91, 11, 188], [122, 182, 24], [153, 102, 133], [202, 185, 107]], ![[0, 1], [215, 132, 182], [106, 67, 189], [87, 151, 67], [75, 0, 147], [135, 57, 192], [219, 127, 38], [105, 53, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 85], []]
 b := ![[], [203, 34, 198], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [71, 229, 171, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-201238, -28680, 9560]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-842, -120, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [30, 12, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [240, 50, 2], [96, 190, 239], [0, 1]]
 g := ![![[233, 42, 9], [29, 191], [66, 231], [200, 161], [104, 99, 27], [51, 27, 108], [1]], ![[141, 35, 108, 221], [133, 98], [146, 83], [146, 181], [73, 28, 192, 75], [138, 65, 225, 223], [53, 215, 155, 8]], ![[1, 220, 158, 29], [199, 5], [208, 233], [60, 2], [3, 150, 7, 60], [90, 192, 168, 106], [11, 143, 74, 233]]]
 h' := ![![[240, 50, 2], [238, 226, 3], [229, 139, 51], [194, 42, 58], [13, 187, 142], [157, 201, 73], [211, 229, 95], [0, 1]], ![[96, 190, 239], [112, 123, 58], [103, 101, 87], [77, 180, 18], [141, 62, 121], [140, 204, 53], [96, 53, 192], [240, 50, 2]], ![[0, 1], [155, 133, 180], [10, 1, 103], [15, 19, 165], [176, 233, 219], [96, 77, 115], [177, 200, 195], [96, 190, 239]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [206, 83], []]
 b := ![[], [154, 217, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [30, 12, 146, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1537580, 810724, 110378]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6380, 3364, 458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [26, 12, 160, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [211, 75, 42], [131, 175, 209], [0, 1]]
 g := ![![[156, 121, 152], [20, 151, 117], [135, 198], [20, 66, 4], [152, 221, 16], [6, 144, 249], [1]], ![[36, 77, 10, 59], [247, 246, 77, 11], [209, 190], [84, 125, 76, 54], [161, 218, 76, 116], [169, 163, 166, 176], [206, 245, 217, 43]], ![[24, 193, 47, 180], [208, 80, 68, 227], [236, 67], [192, 204, 17, 41], [39, 196, 248, 63], [62, 212, 25, 169], [224, 56, 13, 208]]]
 h' := ![![[211, 75, 42], [233, 6, 217], [77, 26, 165], [233, 132, 169], [64, 200, 249], [95, 123, 247], [225, 239, 91], [0, 1]], ![[131, 175, 209], [187, 69, 75], [74, 189, 98], [57, 78, 230], [196, 80, 18], [144, 218, 199], [171, 9, 110], [211, 75, 42]], ![[0, 1], [203, 176, 210], [164, 36, 239], [246, 41, 103], [112, 222, 235], [48, 161, 56], [84, 3, 50], [131, 175, 209]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [181, 248], []]
 b := ![[], [149, 77, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [26, 12, 160, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5221302, -582320, 138552]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20802, -2320, 552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [130, 47, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [213, 147, 149], [251, 109, 108], [0, 1]]
 g := ![![[115, 95, 144], [14, 185], [66, 95], [80, 64], [15, 146], [115, 68], [207, 1], []], ![[164, 224, 148, 180], [127, 29], [57, 95], [167, 114], [233, 128], [89, 46], [23, 59], [49, 99]], ![[35, 29, 155, 166], [141, 184], [246, 123], [168, 158], [250, 232], [26, 1], [189, 21], [90, 99]]]
 h' := ![![[213, 147, 149], [244, 28, 245], [137, 34, 106], [39, 159, 159], [38, 205, 8], [184, 75, 143], [75, 164, 140], [0, 0, 1], [0, 1]], ![[251, 109, 108], [49, 128, 37], [232, 219, 172], [184, 142, 159], [7, 69, 63], [182, 124, 34], [207, 131, 118], [192, 161, 109], [213, 147, 149]], ![[0, 1], [236, 101, 232], [233, 4, 236], [49, 213, 196], [72, 240, 186], [226, 58, 80], [137, 219, 256], [158, 96, 147], [251, 109, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [173, 29], []]
 b := ![[], [38, 87, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [130, 47, 50, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16962, 52942, 15677]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, 206, 61]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀



lemma PB274I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB274I4 : PrimesBelowBoundCertificateInterval O 193 257 274 where
  m := 11
  g := ![1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB274I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
    · exact ![I241N0]
    · exact ![I251N0]
    · exact ![I257N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![199, 199, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![13651919]
    · exact ![13997521]
    · exact ![15813251]
    · exact ![16974593]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I199N0, I199N1, I199N2, I211N1, I227N1, I229N1, I233N1]
  Il := ![[], [I199N0, I199N1, I199N2], [I211N1], [], [I227N1], [I229N1], [I233N1], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
