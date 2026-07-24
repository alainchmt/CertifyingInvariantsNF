
import IdealArithmetic.Examples.NF3_1_656731_1.RI3_1_656731_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84342509190, 936571016, 3377867349]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![84342509190, 936571016, 3377867349]] 
 ![![197, 0, 0], ![0, 197, 0], ![101, 36, 1]] where
  M :=![![![84342509190, 936571016, 3377867349], ![294811030379, 3273692814, 11807006493], ![105126749835, 1167367059, 4210263830]]]
  hmulB := by decide  
  f := ![![![-61911, 15763, 5466]], ![![491305, -193095, 147333]], ![![65196, -28931, 28826]]]
  g := ![![![-1303665447, -612521084, 3377867349], ![-4556835662, -2141007822, 11807006493], ![-1624923335, -763462593, 4210263830]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [68, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [195, 196], [0, 1]]
 g := ![![[29, 63], [6], [95, 187], [24], [100], [156], [195, 1]], ![[100, 134], [6], [115, 10], [24], [100], [156], [193, 196]]]
 h' := ![![[195, 196], [91, 121], [41, 177], [9, 37], [159, 157], [8, 10], [136, 133], [0, 1]], ![[0, 1], [46, 76], [81, 20], [132, 160], [42, 40], [185, 187], [67, 64], [195, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [25, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [68, 2, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2201, 135, -1917]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![994, 351, -1917]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61911, -15763, -5466]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![61911, -15763, -5466]] 
 ![![197, 0, 0], ![69, 1, 0], ![84, 0, 1]] where
  M :=![![![61911, -15763, -5466], ![-491305, 193095, -147333], ![-1409643, 340050, 177332]]]
  hmulB := by decide  
  f := ![![![-84342509190, -936571016, -3377867349]], ![![-31037787637, -344655294, -1243044942]], ![![-36496941735, -405275799, -1461680818]]]
  g := ![![![8166, -15763, -5466], ![-7304, 193095, -147333], ![-201873, 340050, 177332]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![84342509190, 936571016, 3377867349]] ![![61911, -15763, -5466]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105271, 21720, 23548]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-105271, 21720, 23548]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 112, 1]] where
  M :=![![![-105271, 21720, 23548], ![2070396, -670423, 219028], ![2054476, -356444, -648703]]]
  hmulB := by decide  
  f := ![![![2577771999, 28624552, 103238236]], ![![9010351084, 100054335, 360859204]], ![![5087298116, 56491276, 203743265]]]
  g := ![![![-529, -13144, 23548], ![10404, -126641, 219028], ![10324, 363308, -648703]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [163, 166, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 198], [0, 1]]
 g := ![![[117, 100], [55, 72], [8, 160], [28], [46], [184], [33, 1]], ![[34, 99], [43, 127], [114, 39], [28], [46], [184], [66, 198]]]
 h' := ![![[33, 198], [189, 189], [89, 120], [71, 89], [156, 174], [93, 134], [193, 130], [0, 1]], ![[0, 1], [58, 10], [69, 79], [23, 110], [127, 25], [137, 65], [105, 69], [33, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [108, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [163, 166, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3582, 4011, -5474]
  a := ![2, -2, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, 3101, -5474]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2577771999, -28624552, -103238236]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-2577771999, -28624552, -103238236]] 
 ![![199, 0, 0], ![185, 1, 0], ![111, 0, 1]] where
  M :=![![![-2577771999, -28624552, -103238236], ![-9010351084, -100054335, -360859204], ![-3213003676, -35678404, -128678887]]]
  hmulB := by decide  
  f := ![![![105271, -21720, -23548]], ![![87461, -16823, -22992]], ![![48395, -10324, -9875]]]
  g := ![![![71242283, -28624552, -103238236], ![249020465, -100054335, -360859204], ![88798279, -35678404, -128678887]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-105271, 21720, 23548]] ![![-2577771999, -28624552, -103238236]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-12, 32, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-12, 32, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![199, 32, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-12, 32, 1], ![119, -36, 289], ![2791, -761, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-199, -32, 211]], ![![-1, 0, 1], ![-272, -44, 289], ![17, -3, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [118, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [140, 210], [0, 1]]
 g := ![![[31, 45], [185, 19], [194], [193], [5, 100], [47], [140, 1]], ![[1, 166], [102, 192], [194], [193], [79, 111], [47], [69, 210]]]
 h' := ![![[140, 210], [114, 16], [137, 21], [175, 163], [43, 68], [197, 10], [149, 70], [0, 1]], ![[0, 1], [33, 195], [123, 190], [207, 48], [68, 143], [120, 201], [32, 141], [140, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [53, 159]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [118, 71, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1809162, 1925036, -6484878]
  a := ![-65, 1, -521]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6124644, 992612, -6484878]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-78, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-78, 1, 0]] 
 ![![211, 0, 0], ![133, 1, 0], ![4, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-78, 1, 0], ![1, -78, 9], ![87, -24, -77]]]
  hmulB := by decide  
  f := ![![![22351, -2290770, 264330], ![-18990, -6197070, 0]], ![![14067, -1443879, 166608], ![-12026, -3906032, 0]], ![![430, -43427, 5011], ![-343, -117480, 0]]]
  g := ![![![1, 0, 0], ![-133, 211, 0], ![-4, 0, 211]], ![![-1, 1, 0], ![49, -78, 9], ![17, -24, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-12, 32, 1]] ![![211, 0, 0], ![-78, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-16458, 211, 0]], ![![-2532, 6752, 211], ![1055, -2532, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-78, 1, 0]]], ![![![-12, 32, 1]], ![![5, -12, 1]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![5, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![5, 1, 0]] 
 ![![223, 0, 0], ![5, 1, 0], ![146, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![5, 1, 0], ![1, 5, 9], ![87, -24, 6]]]
  hmulB := by decide  
  f := ![![![-13657, -68338, -123012], ![-446, 3047964, 0]], ![![-306, -1530, -2754], ![1, 68238, 0]], ![![-8939, -44741, -80537], ![-397, 1995528, 0]]]
  g := ![![![1, 0, 0], ![-5, 223, 0], ![-146, 0, 223]], ![![0, 1, 0], ![-6, 5, 9], ![-3, -24, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![84, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![84, 1, 0]] 
 ![![223, 0, 0], ![84, 1, 0], ![9, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![84, 1, 0], ![1, 84, 9], ![87, -24, 85]]]
  hmulB := by decide  
  f := ![![![1793, 206968, 22176], ![1784, -549472, 0]], ![![676, 77949, 8352], ![670, -206944, 0]], ![![-9, 8352, 895], ![288, -22176, 0]]]
  g := ![![![1, 0, 0], ![-84, 223, 0], ![-9, 0, 223]], ![![0, 1, 0], ![-32, 84, 9], ![6, -24, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16457340711404, -182748515058, -659106711127]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-16457340711404, -182748515058, -659106711127]] 
 ![![223, 0, 0], ![133, 1, 0], ![116, 0, 1]] where
  M :=![![![-16457340711404, -182748515058, -659106711127], ![-57525032383107, -638779644356, -2303843346649], ![-20512867787935, -227782616497, -821528159414]]]
  hmulB := by decide  
  f := ![![![3701169, -206107, -2391430]], ![![1273520, 151046, -1445321]], ![![1769795, -160098, -970926]]]
  g := ![![![378047490054, -182748515058, -659106711127], ![1321428199675, -638779644356, -2303843346649], ![471208460530, -227782616497, -821528159414]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![5, 1, 0]] ![![223, 0, 0], ![84, 1, 0]]
  ![![3701169, -206107, -2391430]] where
 M := ![![![49729, 0, 0], ![18732, 223, 0]], ![![1115, 223, 0], ![421, 89, 9]]]
 hmul := by decide  
 g := ![![![![-3669986978643092, -40752918857934, -146980796581321]], ![![-1439941652141043, -15989654909228, -57668807081317]]], ![![![-139811735940127, -1552522219646, -5599376902284]], ![![-54855982653314, -609141510025, -2196949491798]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![3701169, -206107, -2391430]] ![![-16457340711404, -182748515058, -659106711127]]
  ![![223, 0, 0]] where
 M := ![![![223, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [169, 114, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 110, 160], [114, 116, 67], [0, 1]]
 g := ![![[135, 167, 9], [175, 134, 71], [59, 11], [151, 28], [115, 192], [54, 0, 1], [1]], ![[24, 111, 190, 139], [217, 6, 45, 108], [142, 169], [213, 64], [202, 87], [55, 113, 219, 81], [50, 132, 183, 12]], ![[66, 169, 0, 197], [96, 119, 108, 72], [49, 85], [106, 43], [213, 192], [219, 24, 189, 145], [182, 24, 197, 215]]]
 h' := ![![[112, 110, 160], [162, 105, 3], [222, 183, 57], [81, 141, 187], [160, 196, 74], [181, 159, 173], [58, 113, 226], [0, 1]], ![[114, 116, 67], [202, 225, 123], [68, 175, 26], [225, 119, 214], [122, 82, 219], [133, 15, 108], [201, 88, 31], [112, 110, 160]], ![[0, 1], [17, 124, 101], [193, 96, 144], [23, 194, 53], [2, 176, 161], [70, 53, 173], [29, 26, 197], [114, 116, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [217, 112], []]
 b := ![[], [159, 183, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [169, 114, 1, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5277523, 2915134, -3951162]
  a := ![-2, 1, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23249, 12842, -17406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44889233, -12833201, -25696]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![44889233, -12833201, -25696]] 
 ![![229, 0, 0], ![0, 229, 0], ![182, 206, 1]] where
  M :=![![![44889233, -12833201, -25696], ![-15068753, 45505937, -115524505], ![-1116668359, 307816952, 32672736]]]
  hmulB := by decide  
  f := ![![![161778185486648, 1796445955936, 6479120146933]], ![![565479898739107, 6279301960256, 22647133750357]], ![![638140321126729, 7086150680695, 25557140468260]]]
  g := ![![![216445, -32925, -25696], ![91748433, 104120323, -115524505], ![-30843259, -28047016, 32672736]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [213, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 228], [0, 1]]
 g := ![![[4, 186], [184], [178, 149], [176], [71], [118, 100], [64, 1]], ![[0, 43], [184], [96, 80], [176], [71], [106, 129], [128, 228]]]
 h' := ![![[64, 228], [120, 84], [100, 111], [126, 81], [150, 136], [56, 206], [108, 219], [0, 1]], ![[0, 1], [0, 145], [105, 118], [43, 148], [152, 93], [187, 23], [155, 10], [64, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [74, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [213, 165, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2183, -28, -3384]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2699, 3044, -3384]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161778185486648, -1796445955936, -6479120146933]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-161778185486648, -1796445955936, -6479120146933]] 
 ![![229, 0, 0], ![206, 1, 0], ![94, 0, 1]] where
  M :=![![![-161778185486648, -1796445955936, -6479120146933], ![-565479898739107, -6279301960256, -22647133750357], ![-201644639194963, -2239138086067, -8075747916192]]]
  hmulB := by decide  
  f := ![![![-44889233, 12833201, 25696]], ![![-40314905, 11345561, 527589]], ![![-13549867, 3923598, -132128]]]
  g := ![![![3569113429030, -1796445955936, -6479120146933], ![12475488548503, -6279301960256, -22647133750357], ![4448638037803, -2239138086067, -8075747916192]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![44889233, -12833201, -25696]] ![![-161778185486648, -1796445955936, -6479120146933]]
  ![![229, 0, 0]] where
 M := ![![![-229, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB230I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 229 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 229 (by omega)

def PB230I4 : PrimesBelowBoundCertificateInterval O 193 229 230 where
  m := 6
  g := ![2, 2, 2, 3, 1, 2]
  P := ![197, 199, 211, 223, 227, 229]
  hP := PB230I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
    · exact ![11697083]
    · exact ![52441, 229]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
  β := ![I197N1, I199N1, I211N1, I223N0, I223N1, I223N2, I229N1]
  Il := ![[I197N1], [I199N1], [I211N1], [I223N0, I223N1, I223N2], [], [I229N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
