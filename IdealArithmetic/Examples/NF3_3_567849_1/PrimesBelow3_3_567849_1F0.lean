
import IdealArithmetic.Examples.NF3_3_567849_1.RI3_3_567849_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-272424, 7816, 6059]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-272424, 7816, 6059]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-272424, 7816, 6059], ![-702844, 20165, 15632], ![-555234, 15930, 12349]]]
  hmulB := by decide  
  f := ![![![175, -86, 23]], ![![-1334, 585, -86]], ![![5655, -2688, 628]]]
  g := ![![![-136212, 7816, 6059], ![-351422, 20165, 15632], ![-277617, 15930, 12349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27993, -12815, 2487]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![27993, -12815, 2487]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![27993, -12815, 2487], ![-288492, 132067, -25630], ![1630786, -746551, 144882]]]
  hmulB := by decide  
  f := ![![![28964, -9507, -2179]], ![![126382, -41478, -9507]], ![![502697, -164977, -37814]]]
  g := ![![![12753, -12815, 2487], ![-131431, 132067, -25630], ![742952, -746551, 144882]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2894443, 949895, 217724]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-2894443, 949895, 217724]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-2894443, 949895, 217724], ![-25255984, 8288480, 1899790], ![-97559828, 32017073, 7338585]]]
  hmulB := by decide  
  f := ![![![-113870, 3277, 2530]], ![![-203675, 5797, 4542]], ![![-173631, 5278, 3785]]]
  g := ![![![-2031031, 949895, 217724], ![-17722127, 8288480, 1899790], ![-68457743, 32017073, 7338585]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-272424, 7816, 6059]] ![![27993, -12815, 2487]]
  ![![113870, -3277, -2530]] where
 M := ![![![113870, -3277, -2530]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![113870, -3277, -2530]] ![![-2894443, 949895, 217724]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![685, -318, 62]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![685, -318, 62]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![685, -318, 62], ![-7192, 3281, -636], ![40484, -18542, 3599]]]
  hmulB := by decide  
  f := ![![![15607, -5122, -1174]], ![![50597, -16605, -3806]], ![![185758, -60962, -13973]]]
  g := ![![![293, -318, 62], ![-3067, 3281, -636], ![17276, -18542, 3599]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-271, 124, -24]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-271, 124, -24]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-271, 124, -24], ![2784, -1275, 248], ![-15776, 7220, -1399]]]
  hmulB := by decide  
  f := ![![![6835, -196, -152]], ![![10434, -299, -232]], ![![4640, -132, -103]]]
  g := ![![![-173, 124, -24], ![1778, -1275, 248], ![-10072, 7220, -1399]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![685, -318, 62]] ![![-271, 124, -24]]
  ![![-2049059, 938030, -182042]] where
 M := ![![![-2049059, 938030, -182042]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-2049059, 938030, -182042]] ![![-271, 124, -24]]
  ![![3, 0, 0]] where
 M := ![![![6038665101, -2764414806, 536485614]]]
 hmul := by decide  
 g := ![![![![2012888367, -921471602, 178828538]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 3, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 1], [3, 2, 4], [0, 1]]
 g := ![![[3, 1, 1], []], ![[0, 3, 4, 4], [0, 1]], ![[2, 3, 1, 1], [2, 1]]]
 h' := ![![[3, 2, 1], [0, 0, 1], [0, 1]], ![[3, 2, 4], [4, 3, 2], [3, 2, 1]], ![[0, 1], [1, 2, 2], [3, 2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [0, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 3, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37530, 29820, -56630]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7506, 5964, -11326]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 4, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 3, 2], [1, 3, 5], [0, 1]]
 g := ![![[2, 3, 2], [1]], ![[1, 0, 2, 2], [6, 2, 4, 1]], ![[0, 1, 2, 3], [6, 5, 5, 6]]]
 h' := ![![[2, 3, 2], [1, 3, 3], [0, 1]], ![[1, 3, 5], [0, 0, 1], [2, 3, 2]], ![[0, 1], [0, 4, 3], [1, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 4, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![343133, -244181, 141400]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49019, -34883, 20200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7069, 3236, -628]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-7069, 3236, -628]] 
 ![![11, 0, 0], ![0, 11, 0], ![7, 9, 1]] where
  M :=![![![-7069, 3236, -628], ![72848, -33349, 6472], ![-411800, 188516, -36585]]]
  hmulB := by decide  
  f := ![![![217, -92, -20]], ![![2320, -815, -184]], ![![2901, -1013, -229]]]
  g := ![![![-243, 808, -628], ![2504, -8327, 6472], ![-14155, 47071, -36585]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[1, 4], [2, 9], [1]], ![[0, 7], [8, 2], [1]]]
 h' := ![![[8, 10], [5, 9], [8, 8], [0, 1]], ![[0, 1], [0, 2], [6, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3965, -58, 172]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![251, -146, 172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![217, -92, -20]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![217, -92, -20]] 
 ![![11, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![217, -92, -20], ![2320, -815, -184], ![9512, -3164, -723]]]
  hmulB := by decide  
  f := ![![![-7069, 3236, -628]], ![![4052, -1855, 360]], ![![-38079, 17432, -3383]]]
  g := ![![![55, -92, -20], ![524, -815, -184], ![2081, -3164, -723]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-7069, 3236, -628]] ![![217, -92, -20]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [11, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10, 12], [5, 2, 1], [0, 1]]
 g := ![![[10, 5, 12], [1, 1], [1]], ![[8, 11, 6, 3], [7, 1], [11, 3, 5, 12]], ![[9, 9, 8, 1], [3, 4], [5, 8, 5, 1]]]
 h' := ![![[7, 10, 12], [6, 10, 8], [2, 12, 12], [0, 1]], ![[5, 2, 1], [2, 0, 6], [1, 9, 12], [7, 10, 12]], ![[0, 1], [5, 3, 12], [5, 5, 2], [5, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 10], []]
 b := ![[], [0, 2, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [11, 1, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-365560, 351494, -266929]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28120, 27038, -20533]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29424985, -9656658, -2213388]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![29424985, -9656658, -2213388]] 
 ![![17, 0, 0], ![2, 1, 0], ![14, 0, 1]] where
  M :=![![![29424985, -9656658, -2213388], ![256753008, -84260909, -19313316], ![991795824, -325486422, -74604251]]]
  hmulB := by decide  
  f := ![![![117271193, -3364578, -2608236]], ![![31593986, -906449, -702684]], ![![110635886, -3174210, -2460659]]]
  g := ![![![4689749, -9656658, -2213388], ![40921250, -84260909, -19313316], ![158072246, -325486422, -74604251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-363, 10, 8]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-363, 10, 8]] 
 ![![17, 0, 0], ![6, 1, 0], ![13, 0, 1]] where
  M :=![![![-363, 10, 8], ![-928, 23, 20], ![-696, 6, 13]]]
  hmulB := by decide  
  f := ![![![-179, 82, -16]], ![![46, -21, 4]], ![![-751, 344, -67]]]
  g := ![![![-31, 10, 8], ![-78, 23, 20], ![-53, 6, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![365675, -10588, -8108]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![365675, -10588, -8108]] 
 ![![17, 0, 0], ![8, 1, 0], ![15, 0, 1]] where
  M :=![![![365675, -10588, -8108], ![940528, -25989, -21176], ![757944, -27372, -15401]]]
  hmulB := by decide  
  f := ![![![179372883, -58866388, -13492676]], ![![176478440, -57916493, -13274952]], ![![513912885, -168655344, -38657237]]]
  g := ![![![33647, -10588, -8108], ![86240, -25989, -21176], ![71055, -27372, -15401]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![29424985, -9656658, -2213388]] ![![-363, 10, 8]]
  ![![-179372883, 58866388, 13492676]] where
 M := ![![![-179372883, 58866388, 13492676]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-179372883, 58866388, 13492676]] ![![365675, -10588, -8108]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-944413, 309938, 71038]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-944413, 309938, 71038]] 
 ![![19, 0, 0], ![0, 19, 0], ![6, 3, 1]] where
  M :=![![![-944413, 309938, 71038], ![-8240408, 2704311, 619876], ![-31832604, 10446882, 2394373]]]
  hmulB := by decide  
  f := ![![![-33799191, 969718, 751730]], ![![-87200680, 2501837, 1939436]], ![![-28067586, 805275, 624253]]]
  g := ![![![-72139, 5096, 71038], ![-629456, 44457, 619876], ![-2431518, 171777, 2394373]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [16, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 18], [0, 1]]
 g := ![![[13, 6], [8, 11], [1], [1]], ![[0, 13], [0, 8], [1], [1]]]
 h' := ![![[1, 18], [5, 14], [12, 7], [3, 1], [0, 1]], ![[0, 1], [0, 5], [0, 12], [4, 18], [1, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [3, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [16, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-854, 10, 377]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-164, -59, 377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33799191, -969718, -751730]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![33799191, -969718, -751730]] 
 ![![19, 0, 0], ![13, 1, 0], ![4, 0, 1]] where
  M :=![![![33799191, -969718, -751730], ![87200680, -2501837, -1939436], ![68886948, -1976406, -1532119]]]
  hmulB := by decide  
  f := ![![![944413, -309938, -71038]], ![![1079883, -354395, -81230]], ![![1874224, -615086, -140975]]]
  g := ![![![2600655, -969718, -751730], ![6709595, -2501837, -1939436], ![5300458, -1976406, -1532119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-944413, 309938, 71038]] ![![33799191, -969718, -751730]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5966351, -171178, -132698]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![5966351, -171178, -132698]] 
 ![![23, 0, 0], ![5, 1, 0], ![8, 0, 1]] where
  M :=![![![5966351, -171178, -132698], ![15392968, -441633, -342356], ![12160164, -348882, -270455]]]
  hmulB := by decide  
  f := ![![![-7023, 2354, 466]], ![![-3877, 1261, 306]], ![![-13140, 4454, 809]]]
  g := ![![![342775, -171178, -132698], ![884347, -441633, -342356], ![698618, -348882, -270455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15197, 436, 338]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-15197, 436, 338]] 
 ![![23, 0, 0], ![18, 1, 0], ![13, 0, 1]] where
  M :=![![![-15197, 436, 338], ![-39208, 1125, 872], ![-30972, 888, 689]]]
  hmulB := by decide  
  f := ![![![789, -260, -58]], ![![910, -299, -68]], ![![1611, -532, -117]]]
  g := ![![![-1193, 436, 338], ![-3078, 1125, 872], ![-2431, 888, 689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-180459165, 5177476, 4013604]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-180459165, 5177476, 4013604]] 
 ![![23, 0, 0], ![22, 1, 0], ![0, 0, 1]] where
  M :=![![![-180459165, 5177476, 4013604], ![-465578064, 13357699, 10354952], ![-367798184, 10552340, 8180223]]]
  hmulB := by decide  
  f := ![![![-17600803, 5776212, 1323956]], ![![-23512894, 7716435, 1768672]], ![![-25793528, 8464892, 1940223]]]
  g := ![![![-12798419, 5177476, 4013604], ![-33019454, 13357699, 10354952], ![-26084768, 10552340, 8180223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![5966351, -171178, -132698]] ![![-15197, 436, 338]]
  ![![-79849166667, 2290917962, 1775930500]] where
 M := ![![![-79849166667, 2290917962, 1775930500]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-79849166667, 2290917962, 1775930500]] ![![-180459165, 5177476, 4013604]]
  ![![23, 0, 0]] where
 M := ![![![12689728780331655487, -364075529015933054, -282233081676388544]]]
 hmul := by decide  
 g := ![![![![551727338275289369, -15829370826779698, -12271003551147328]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2964699, 1357216, -263394]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-2964699, 1357216, -263394]] 
 ![![29, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-2964699, 1357216, -263394], ![30553704, -13987001, 2714432], ![-172713908, 79066004, -15344217]]]
  hmulB := by decide  
  f := ![![![287153489, -94237704, -21600082]], ![![86400328, -28354761, -6499152]], ![![333750652, -109529908, -25105185]]]
  g := ![![![-102231, 1357216, -263394], ![1053576, -13987001, 2714432], ![-5955652, 79066004, -15344217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-590439, 16940, 13132]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-590439, 16940, 13132]] 
 ![![29, 0, 0], ![14, 1, 0], ![11, 0, 1]] where
  M :=![![![-590439, 16940, 13132], ![-1523312, 43705, 33880], ![-1203384, 34524, 26765]]]
  hmulB := by decide  
  f := ![![![91205, -29932, -6860]], ![![71470, -23455, -5376]], ![![140603, -46144, -10575]]]
  g := ![![![-33519, 16940, 13132], ![-86478, 43705, 33880], ![-68315, 34524, 26765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-2964699, 1357216, -263394]] ![![-590439, 16940, 13132]]
  ![![-25381235, 1709764, 310402]] where
 M := ![![![-25381235, 1709764, 310402]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-25381235, 1709764, 310402]] ![![-590439, 16940, 13132]]
  ![![29, 0, 0]] where
 M := ![![![12008034193429, -344516566632, -267071664170]]]
 hmul := by decide  
 g := ![![![![414070144601, -11879881608, -9209367730]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63063655, 28865610, -5601642]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-63063655, 28865610, -5601642]] 
 ![![31, 0, 0], ![0, 31, 0], ![19, 10, 1]] where
  M :=![![![-63063655, 28865610, -5601642], ![649790472, -297475219, 57731220], ![-3673305996, 1681578906, -326340829]]]
  hmulB := by decide  
  f := ![![![41683684799, -13679704098, -3135504342]], ![![363718503672, -119364723373, -27359408196]], ![![188198757143, -61762853302, -14156570443]]]
  g := ![![![1398953, 2738130, -5601642], ![-14422668, -28218949, 57731220], ![81521605, 159515716, -326340829]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [21, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 30], [0, 1]]
 g := ![![[21, 2], [7, 28], [16, 9], [24, 1]], ![[7, 29], [28, 3], [15, 22], [17, 30]]]
 h' := ![![[24, 30], [8, 8], [5, 11], [23, 28], [0, 1]], ![[0, 1], [14, 23], [21, 20], [13, 3], [24, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [25, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [21, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71833, 14482, 21716]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15627, -6538, 21716]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60230769, -27572288, 5350878]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![60230769, -27572288, 5350878]] 
 ![![31, 0, 0], ![11, 1, 0], ![27, 0, 1]] where
  M :=![![![60230769, -27572288, 5350878], ![-620701848, 284149747, -55144576], ![3508736332, -1606248460, 311722035]]]
  hmulB := by decide  
  f := ![![![152897777815, -50177818200, -11501182022]], ![![97290731307, -31928761149, -7318343182]], ![![299412850159, -98260967404, -22522248123]]]
  g := ![![![7066201, -27572288, 5350878], ![-72820823, 284149747, -55144576], ![411644337, -1606248460, 311722035]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-63063655, 28865610, -5601642]] ![![60230769, -27572288, 5350878]]
  ![![31, 0, 0]] where
 M := ![![![-41369994711505119, 18938593872464630, -3675382992151920]]]
 hmul := by decide  
 g := ![![![![-1334515958435649, 610922382982730, -118560741682320]]]]
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


lemma PB168I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB168I0 : PrimesBelowBoundCertificateInterval O 1 31 168 where
  m := 11
  g := ![3, 3, 1, 1, 2, 1, 3, 2, 3, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB168I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0, I29N1, I29N1]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![343]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![17, 17, 17]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![29, 29, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N0, I11N1, I17N0, I17N1, I17N2, I19N1, I23N0, I23N1, I23N2, I29N0, I29N1, I31N1]
  Il := ![[I2N0, I2N1, I2N2], [I3N0, I3N1, I3N1], [I5N0], [], [I11N0, I11N1], [], [I17N0, I17N1, I17N2], [I19N1], [I23N0, I23N1, I23N2], [I29N0, I29N1, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
