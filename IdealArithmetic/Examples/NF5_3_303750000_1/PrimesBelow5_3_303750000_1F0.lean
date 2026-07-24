
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 21, -50, 37, -44]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-5, 21, -50, 37, -44]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-5, 21, -50, 37, -44], ![28, -87, 238, -168, 208], ![-28, 123, -297, 219, -262], ![160, -487, 1344, -946, 1174], ![-20, 161, -330, 259, -295]]]
  hmulB := by decide  
  f := ![![![10, -37, 34, 11, -14]], ![![-40, -56, -76, -1, 30]], ![![-1, 44, -3, -8, 2]], ![![75, 78, 146, 7, -58]], ![![51, -33, 110, 21, -45]]]
  g := ![![![26, 21, -50, 37, -44], ![-125, -87, 238, -168, 208], ![156, 123, -297, 219, -262], ![-706, -487, 1344, -946, 1174], ![173, 161, -330, 259, -295]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -2, -2, 0, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-4, -2, -2, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-4, -2, -2, 0, 1], ![-2, 2, -5, -1, 2], ![4, 4, 5, 0, -2], ![6, -3, 9, 2, -4], ![0, -6, 0, 1, 0]]]
  hmulB := by decide  
  f := ![![![0, 1, 1, 0, 1]], ![![2, 3, 2, 1, 1]], ![![2, 2, 3, 0, 2]], ![![12, 18, 12, 6, 7]], ![![9, 12, 12, 2, 8]]]
  g := ![![![-2, -2, -2, 0, 1], ![-1, 2, -5, -1, 2], ![2, 4, 5, 0, -2], ![3, -3, 9, 2, -4], ![0, -6, 0, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -94, 239, -173, 210]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![25, -94, 239, -173, 210]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![25, -94, 239, -173, 210], ![-114, 433, -1097, 795, -964], ![148, -557, 1416, -1025, 1244], ![-642, 2440, -6181, 4480, -5432], ![174, -647, 1652, -1194, 1451]]]
  hmulB := by decide  
  f := ![![![194, 11, 39, 7, -28]], ![![87, 15, 22, 2, -14]], ![![-42, -7, -3, 0, 4]], ![![39, -14, -2, 3, -2]], ![![81, 1, 4, 2, -7]]]
  g := ![![![41, -94, 239, -173, 210], ![-189, 433, -1097, 795, -964], ![243, -557, 1416, -1025, 1244], ![-1065, 2440, -6181, 4480, -5432], ![282, -647, 1652, -1194, 1451]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-5, 21, -50, 37, -44]] ![![-4, -2, -2, 0, 1]]
  ![![0, 5, -12, 9, -11]] where
 M := ![![![0, 5, -12, 9, -11]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![0, 5, -12, 9, -11]] ![![-4, -2, -2, 0, 1]]
  ![![-4, 1, -4, 2, -2]] where
 M := ![![![-4, 1, -4, 2, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-4, 1, -4, 2, -2]] ![![25, -94, 239, -173, 210]]
  ![![-2438, 9211, -23383, 16935, -20546]] where
 M := ![![![-2438, 9211, -23383, 16935, -20546]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-2438, 9211, -23383, 16935, -20546]] ![![25, -94, 239, -173, 210]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-19018962, 71856528, -182414704, 132112818, -160283002]]]
 hmul := by decide  
 g := ![![![![-9509481, 35928264, -91207352, 66056409, -80141501]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 3, 1, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![1, 3, 1, 0, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1, 3, 1, 0, 1], ![8, 9, 12, 2, 2], ![4, 2, 5, 2, 4], ![28, 42, 32, 9, 30], ![22, 36, 26, 6, 21]]]
  hmulB := by decide  
  f := ![![![81, 3, 21, 2, -11]], ![![-4, 1, -4, 2, -2]], ![![42, 0, 15, -2, -2]], ![![38, 8, -6, 13, -20]], ![![52, 0, 18, -2, -3]]]
  g := ![![![-1, 3, 1, 0, 1], ![-8, 9, 12, 2, 2], ![-6, 2, 5, 2, 4], ![-38, 42, 32, 9, 30], ![-28, 36, 26, 6, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![427, 21, 101, 18, -67]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![427, 21, 101, 18, -67]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![427, 21, 101, 18, -67], ![-56, -1, -12, -2, 10], ![-196, -8, -45, -8, 32], ![-220, 0, -44, -7, 42], ![-34, 6, -2, 0, 11]]]
  hmulB := by decide  
  f := ![![![-5, 13, -11, -4, 5]], ![![6, 21, 10, -2, -4]], ![![-2, -6, -3, 0, 2]], ![![-16, -20, -32, 1, 10]], ![![-10, 4, -20, -4, 9]]]
  g := ![![![61, 21, 101, 18, -67], ![-10, -1, -12, -2, 10], ![-30, -8, -45, -8, 32], ![-44, 0, -44, -7, 42], ![-14, 6, -2, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![1, 3, 1, 0, 1]] ![![1, 3, 1, 0, 1]]
  ![![51, 68, 68, 14, 32]] where
 M := ![![![51, 68, 68, 14, 32]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![51, 68, 68, 14, 32]] ![![427, 21, 101, 18, -67]]
  ![![473, 651, 595, 140, 379]] where
 M := ![![![473, 651, 595, 140, 379]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![473, 651, 595, 140, 379]] ![![427, 21, 101, 18, -67]]
  ![![5209, 6796, 6268, 1472, 3908]] where
 M := ![![![5209, 6796, 6268, 1472, 3908]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![5209, 6796, 6268, 1472, 3908]] ![![427, 21, 101, 18, -67]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![158427, 75897, 89913, 19722, 24345]]]
 hmul := by decide  
 g := ![![![![52809, 25299, 29971, 6574, 8115]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![215, 11, 51, 9, -34]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![215, 11, 51, 9, -34]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![215, 11, 51, 9, -34], ![-28, -2, -5, -1, 4], ![-100, -6, -25, -4, 16], ![-116, -5, -29, -6, 20], ![-20, 1, -5, -1, 3]]]
  hmulB := by decide  
  f := ![![![23, 31, 29, 7, 18]], ![![27, 37, 34, 8, 22]], ![![20, 28, 25, 6, 16]], ![![147, 202, 186, 43, 118]], ![![104, 143, 131, 31, 83]]]
  g := ![![![39, 11, 51, 9, -34], ![-5, -2, -5, -1, 4], ![-18, -6, -25, -4, 16], ![-21, -5, -29, -6, 20], ![-4, 1, -5, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![215, 11, 51, 9, -34]] ![![215, 11, 51, 9, -34]]
  ![![40453, 1958, 9544, 1700, -6372]] where
 M := ![![![40453, 1958, 9544, 1700, -6372]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![40453, 1958, 9544, 1700, -6372]] ![![215, 11, 51, 9, -34]]
  ![![7618411, 368931, 1797273, 320115, -1199982]] where
 M := ![![![7618411, 368931, 1797273, 320115, -1199982]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![7618411, 368931, 1797273, 320115, -1199982]] ![![215, 11, 51, 9, -34]]
  ![![1434767297, 69480464, 338479056, 60286968, -225991528]] where
 M := ![![![1434767297, 69480464, 338479056, 60286968, -225991528]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![1434767297, 69480464, 338479056, 60286968, -225991528]] ![![215, 11, 51, 9, -34]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![270208152535, 13085178635, 63745388995, 11353778705, -42560736570]]]
 hmul := by decide  
 g := ![![![![54041630507, 2617035727, 12749077799, 2270755741, -8512147314]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, -516, 1310, -948, 1150]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![137, -516, 1310, -948, 1150]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![2, 1, 4, 2, 1]] where
  M :=![![![137, -516, 1310, -948, 1150], ![-628, 2367, -6016, 4356, -5284], ![808, -3054, 7755, -5618, 6816], ![-3532, 13354, -33888, 24545, -29780], ![944, -3560, 9042, -6546, 7941]]]
  hmulB := by decide  
  f := ![![![79, 8, 22, 4, -10]], ![![4, 17, 16, 4, 12]], ![![-24, 14, 5, 2, 16]], ![![44, 118, 96, 23, 76]], ![![30, 59, 50, 12, 37]]]
  g := ![![![-309, -238, -470, -464, 1150], ![1420, 1093, 2160, 2132, -5284], ![-1832, -1410, -2787, -2750, 6816], ![8004, 6162, 12176, 12015, -29780], ![-2134, -1643, -3246, -3204, 7941]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 0, 2, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 0, 3, 5], [0, 6, 6, 4], [6, 0, 5, 5], [0, 1]]
 g := ![![[6, 0, 4, 1], []], ![[0, 3, 0, 3, 5, 6], [4, 1, 5, 6, 4, 6]], ![[3, 2, 4, 2, 4, 4], [6, 0, 4, 3, 5, 1]], ![[0, 4, 2, 2, 3, 3], [4, 6, 4, 6, 0, 6]]]
 h' := ![![[5, 0, 3, 5], [0, 0, 0, 1], [0, 1]], ![[0, 6, 6, 4], [0, 2, 3, 2], [5, 0, 3, 5]], ![[6, 0, 5, 5], [5, 0, 3, 1], [0, 6, 6, 4]], ![[0, 1], [0, 5, 1, 3], [6, 0, 5, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 3, 4], []]
 b := ![[], [], [4, 4, 3, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 0, 2, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1167223286281, 1405833678247, 1797650271213, 61413736884, 1236877283101]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-186647325703, 24136627878, -449979837313, -344620118474, 1236877283101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -8, -22, -4, 10]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-79, -8, -22, -4, 10]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-79, -8, -22, -4, 10], ![-4, -17, -16, -4, -12], ![24, -14, -5, -2, -16], ![-44, -118, -96, -23, -76], ![-56, -88, -78, -18, -51]]]
  hmulB := by decide  
  f := ![![![-137, 516, -1310, 948, -1150]], ![![31, -117, 298, -216, 262]], ![![-135, 510, -1295, 938, -1138]], ![![485, -1834, 4654, -3371, 4090]], ![![-174, 656, -1666, 1206, -1463]]]
  g := ![![![-7, -8, -22, -4, 10], ![13, -17, -16, -4, -12], ![15, -14, -5, -2, -16], ![83, -118, -96, -23, -76], ![58, -88, -78, -18, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![137, -516, 1310, -948, 1150]] ![![-79, -8, -22, -4, 10]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 10, 50, -17, 39]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![19, 10, 50, -17, 39]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![10, 4, 1, 0, 0], ![1, 8, 0, 1, 0], ![7, 2, 0, 0, 1]] where
  M :=![![![19, 10, 50, -17, 39], ![64, 162, -39, 123, -58], ![88, 26, 265, -108, 212], ![412, 985, -155, 708, -286], ![382, 415, 661, -43, 471]]]
  hmulB := by decide  
  f := ![![![6103, 300, 1450, 257, -965]], ![![-816, -66, -187, -29, 126]], ![![4994, 236, 1187, 212, -790]], ![![-335, -31, -75, -11, 51]], ![![3685, 179, 879, 156, -584]]]
  g := ![![![-67, -12, 50, -17, 39], ![67, -50, -39, 123, -58], ![-358, -54, 265, -108, 212], ![296, -317, -155, 708, -286], ![-862, -257, 661, -43, 471]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 3, 1] where
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
 g := ![![[4, 5], [5, 9], [1]], ![[0, 6], [0, 2], [1]]]
 h' := ![![[8, 10], [10, 7], [2, 8], [0, 1]], ![[0, 1], [0, 4], [0, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5797, 6568, 10124, -965, 7983]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13669, -3834, 10124, -965, 7983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6103, 300, 1450, 257, -965]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![6103, 300, 1450, 257, -965]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![5, 6, 7, 1, 0], ![0, 4, 1, 0, 1]] where
  M :=![![![6103, 300, 1450, 257, -965], ![-816, -66, -187, -29, 126], ![-2832, -140, -695, -122, 456], ![-3260, -113, -779, -146, 518], ![-554, 1, -107, -25, 79]]]
  hmulB := by decide  
  f := ![![![19, 10, 50, -17, 39]], ![![64, 162, -39, 123, -58]], ![![88, 26, 265, -108, 212]], ![![137, 199, 156, 55, 95]], ![![66, 99, 70, 31, 41]]]
  g := ![![![438, 238, 56, 257, -965], ![-61, -36, -10, -29, 126], ![-202, -112, -27, -122, 456], ![-230, -119, -25, -146, 518], ![-39, -15, -1, -25, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 3 2 3 [6, 6, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 1, 7], [6, 9, 4], [0, 1]]
 g := ![![[2, 6, 5], [8, 5, 1], []], ![[10, 5, 2, 2], [3, 7, 2, 6], [6, 5]], ![[3, 4], [4, 5, 1, 4], [9, 5]]]
 h' := ![![[10, 1, 7], [7, 10, 4], [0, 0, 1], [0, 1]], ![[6, 9, 4], [0, 2, 7], [9, 9, 9], [10, 1, 7]], ![[0, 1], [6, 10], [4, 2, 1], [6, 9, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 5], []]
 b := ![[], [9, 7, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 3
  hpos := by decide
  P := [6, 6, 6, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1812618170, 2052594993, 3022995486, -112427139, 2152543398]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![215886715, -534819615, 150676551, -112427139, 2152543398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![19, 10, 50, -17, 39]] ![![6103, 300, 1450, 257, -965]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![555, 160, 234, 49, 9]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![555, 160, 234, 49, 9]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![1, 12, 0, 4, 1]] where
  M :=![![![555, 160, 234, 49, 9], ![436, 682, 611, 145, 410], ![232, 600, 507, 122, 388], ![2888, 4301, 3887, 918, 2550], ![2246, 3149, 2873, 677, 1843]]]
  hmulB := by decide  
  f := ![![![9, -30, 82, -59, 71]], ![![-36, 146, -367, 271, -330]], ![![48, -194, 477, -348, 424]], ![![-224, 829, -2111, 1520, -1842]], ![![-97, 371, -939, 682, -828]]]
  g := ![![![42, 4, 18, 1, 9], ![2, -326, 47, -115, 410], ![-12, -312, 39, -110, 388], ![26, -2023, 299, -714, 2550], ![31, -1459, 221, -515, 1843]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [12, 8, 4, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 4, 12, 5], [3, 0, 2, 7], [6, 8, 12, 1], [0, 1]]
 g := ![![[12, 10, 9, 4], [8, 8, 1], []], ![[7, 1, 3, 9, 0, 11], [12, 10, 9], [9, 2, 5, 0, 2, 8]], ![[7, 9, 2, 0, 9, 6], [2, 0, 10], [12, 6, 5, 6, 9, 5]], ![[2, 10, 7, 1, 4, 9], [1, 10, 3], [12, 4, 3, 11, 5, 1]]]
 h' := ![![[12, 4, 12, 5], [8, 9, 9, 11], [0, 0, 0, 1], [0, 1]], ![[3, 0, 2, 7], [11, 0, 0, 7], [8, 7, 6, 10], [12, 4, 12, 5]], ![[6, 8, 12, 1], [2, 10, 3, 5], [0, 1, 2, 6], [3, 0, 2, 7]], ![[0, 1], [11, 7, 1, 3], [7, 5, 5, 9], [6, 8, 12, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 11, 6], []]
 b := ![[], [], [12, 1, 5, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [12, 8, 4, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1413651110382, 1644535385645, 2272720978853, -9281713750, 1587415796555]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13366514321, -1338804167155, 174824690681, -489149607690, 1587415796555]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -30, 82, -59, 71]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![9, -30, 82, -59, 71]] 
 ![![13, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![9, -30, 82, -59, 71], ![-36, 146, -367, 271, -330], ![48, -194, 477, -348, 424], ![-224, 829, -2111, 1520, -1842], ![58, -215, 559, -407, 493]]]
  hmulB := by decide  
  f := ![![![555, 160, 234, 49, 9]], ![![247, 114, 137, 30, 35]], ![![274, 120, 147, 32, 34]], ![![521, 417, 425, 97, 201]], ![![557, 353, 383, 86, 148]]]
  g := ![![![-43, -30, 82, -59, 71], ![193, 146, -367, 271, -330], ![-248, -194, 477, -348, 424], ![1095, 829, -2111, 1520, -1842], ![-293, -215, 559, -407, 493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![555, 160, 234, 49, 9]] ![![9, -30, 82, -59, 71]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 2, 40, 8, -26]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![157, 2, 40, 8, -26]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![10, 6, 11, 1, 0], ![16, 7, 11, 0, 1]] where
  M :=![![![157, 2, 40, 8, -26], ![-32, -13, -26, -2, 12], ![-72, 14, -19, -6, 12], ![-64, 16, 18, -3, 0], ![-4, -8, 18, 4, -7]]]
  hmulB := by decide  
  f := ![![![13, 18, 16, 4, 10]], ![![64, 87, 82, 18, 52]], ![![56, 78, 69, 18, 44]], ![![90, 124, 113, 27, 72]], ![![92, 127, 115, 28, 73]]]
  g := ![![![29, 8, 14, 8, -26], ![-12, -5, -8, -2, 12], ![-12, -2, -5, -6, 12], ![-2, 2, 3, -3, 0], ![4, 1, 3, 4, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [9, 8, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 8, 7], [10, 8, 10], [0, 1]]
 g := ![![[13, 5, 13], [], [12, 1], []], ![[16, 7, 5, 7], [10, 16], [11, 13], [3, 15]], ![[14, 0, 11, 14], [0, 16], [12, 13], [0, 15]]]
 h' := ![![[2, 8, 7], [2, 2, 9], [11, 14], [0, 0, 1], [0, 1]], ![[10, 8, 10], [3, 12, 1], [5, 10, 13], [11, 9, 8], [2, 8, 7]], ![[0, 1], [4, 3, 7], [15, 10, 4], [15, 8, 8], [10, 8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 7], []]
 b := ![[], [0, 3, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [9, 8, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1929037, -2999676, 11610376, -7382312, 9763776]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4733427, -1591308, -857984, -7382312, 9763776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 17, -19, 28, -41]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![63, 17, -19, 28, -41]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![63, 17, -19, 28, -41], ![8, -63, 158, -116, 142], ![-52, 80, -213, 148, -176], ![60, -354, 894, -653, 798], ![-30, 96, -240, 174, -209]]]
  hmulB := by decide  
  f := ![![![229, -97, 467, 82, -191]], ![![97, -124, 205, 50, -85]], ![![136, -32, 275, 44, -112]], ![![243, 39, 483, 61, -195]], ![![266, -62, 538, 86, -219]]]
  g := ![![![22, 17, -19, 28, -41], ![-109, -63, 158, -116, 142], ![140, 80, -213, 148, -176], ![-615, -354, 894, -653, 798], ![160, 96, -240, 174, -209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127, 203, -273, -73, 114]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-127, 203, -273, -73, 114]] 
 ![![17, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-127, 203, -273, -73, 114], ![488, 814, 907, -13, -356], ![164, -750, 395, 184, -172], ![-824, -1397, -1529, 26, 600], ![-632, 43, -1271, -185, 517]]]
  hmulB := by decide  
  f := ![![![1709, 2251, 2069, 489, 1294]], ![![1882, 2508, 2303, 543, 1448]], ![![2028, 2700, 2477, 586, 1556]], ![![3990, 5437, 4983, 1170, 3164]], ![![2786, 3803, 3479, 821, 2209]]]
  g := ![![![85, 203, -273, -73, 114], ![-1362, 814, 907, -13, -356], ![208, -750, 395, 184, -172], ![2314, -1397, -1529, 26, 600], ![1050, 43, -1271, -185, 517]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![157, 2, 40, 8, -26]] ![![63, 17, -19, 28, -41]]
  ![![9087, 415, 2205, 336, -1375]] where
 M := ![![![9087, 415, 2205, 336, -1375]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![9087, 415, 2205, 336, -1375]] ![![-127, 203, -273, -73, 114]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![2227, 204, 510, 85, -357]]]
 hmul := by decide  
 g := ![![![![131, 12, 30, 5, -21]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, -62, 224, 42, -92]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![109, -62, 224, 42, -92]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![8, 10, 6, 1, 0], ![13, 4, 16, 0, 1]] where
  M :=![![![109, -62, 224, 42, -92], ![-224, -603, -396, 48, 152], ![-200, 338, -431, -118, 180], ![376, 1030, 664, -85, -252], ![424, 202, 832, 82, -335]]]
  hmulB := by decide  
  f := ![![![-1393, -66, -328, -58, 220]], ![![192, 15, 52, 8, -24]], ![![648, 38, 155, 30, -100]], ![![-240, -4, -50, -9, 44]], ![![-359, -8, -80, -12, 61]]]
  g := ![![![51, -6, 76, 42, -92], ![-136, -89, -164, 48, 152], ![-84, 42, -137, -118, 180], ![228, 152, 274, -85, -252], ![217, 38, 300, 82, -335]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [14, 3, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 5, 16], [12, 13, 3], [0, 1]]
 g := ![![[6, 5, 16], [5, 0, 17], [4, 1], []], ![[6, 13, 11, 4], [6, 7], [1, 17], [6, 9]], ![[5, 18, 0, 18], [17, 14, 8, 13], [3, 6], [0, 9]]]
 h' := ![![[11, 5, 16], [6, 5, 15], [1, 12, 13], [0, 0, 1], [0, 1]], ![[12, 13, 3], [8, 9, 9], [6, 17], [18, 4, 13], [11, 5, 16]], ![[0, 1], [3, 5, 14], [3, 9, 6], [11, 15, 5], [12, 13, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 2], []]
 b := ![[], [15, 10, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [14, 3, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3403534808, 4114370233, 5233637685, 176833841, 3638305089]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2384689583, -642483607, -2844223515, 176833841, 3638305089]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 81, 75, 17, 48]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![59, 81, 75, 17, 48]] 
 ![![19, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![59, 81, 75, 17, 48], ![292, 404, 365, 89, 232], ![260, 356, 331, 74, 212], ![1836, 2539, 2297, 558, 1460], ![1344, 1849, 1697, 395, 1083]]]
  hmulB := by decide  
  f := ![![![-291, 63, -49, -23, 40]], ![![-206, 46, -23, -15, 24]], ![![-73, 7, -18, -5, 12]], ![![-94, 21, -35, -10, 20]], ![![-184, 51, -35, -17, 27]]]
  g := ![![![-112, 81, 75, 17, 48], ![-553, 404, 365, 89, 232], ![-493, 356, 331, 74, 212], ![-3477, 2539, 2297, 558, 1460], ![-2547, 1849, 1697, 395, 1083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19681, -953, -4643, -827, 3100]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-19681, -953, -4643, -827, 3100]] 
 ![![19, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-19681, -953, -4643, -827, 3100], ![2640, 128, 623, 111, -416], ![9092, 440, 2145, 382, -1432], ![10512, 509, 2479, 442, -1656], ![1836, 89, 433, 77, -289]]]
  hmulB := by decide  
  f := ![![![-31, -55, -39, -7, -20]], ![![-38, -62, -49, -9, -24]], ![![-22, -36, -27, -6, -16]], ![![-44, -63, -55, -12, -40]], ![![-61, -98, -76, -16, -45]]]
  g := ![![![-463, -953, -4643, -827, 3100], ![62, 128, 623, 111, -416], ![214, 440, 2145, 382, -1432], ![248, 509, 2479, 442, -1656], ![43, 89, 433, 77, -289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![109, -62, 224, 42, -92]] ![![59, 81, 75, 17, 48]]
  ![![31, 55, 39, 7, 20]] where
 M := ![![![31, 55, 39, 7, 20]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![31, 55, 39, 7, 20]] ![![-19681, -953, -4643, -827, 3100]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [14, 20, 2, 21, 17, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 22, 21, 0, 20], [22, 17, 5, 13, 2], [8, 15, 8, 1], [13, 14, 12, 9, 1], [0, 1]]
 g := ![![[1, 20, 1, 6, 1], [0, 4, 20, 10, 13], [1], []], ![[19, 15, 14, 9, 18, 5, 3, 11], [0, 14, 10, 2, 2, 20, 16, 11], [2, 7, 17, 6, 14, 17, 10, 17], [12, 9, 8, 9]], ![[15, 4, 11, 3, 8, 6, 0, 12], [17, 14, 8, 4, 11, 12, 4, 1], [18, 12, 7, 7, 20, 6, 11, 18], [5, 9, 7, 4]], ![[14, 8, 7, 4, 9, 5, 18], [7, 4, 7, 1, 10, 14, 8], [16, 1, 13, 21, 18, 14, 4], [22, 1]], ![[17, 10, 18, 2, 19, 17, 15, 13], [17, 10, 0, 22, 17, 19, 18, 18], [18, 14, 7, 14, 2, 15, 15, 13], [2, 21, 1, 1]]]
 h' := ![![[9, 22, 21, 0, 20], [0, 2, 16, 0, 1], [9, 3, 21, 2, 6], [0, 0, 1], [0, 1]], ![[22, 17, 5, 13, 2], [3, 8, 18, 11, 2], [13, 7, 20, 15, 21], [5, 7, 17, 0, 5], [9, 22, 21, 0, 20]], ![[8, 15, 8, 1], [14, 8, 21, 6, 11], [1, 1, 14, 21, 14], [0, 16, 14, 9, 3], [22, 17, 5, 13, 2]], ![[13, 14, 12, 9, 1], [12, 5, 17, 14, 15], [10, 11, 6, 21, 13], [9, 16, 13, 22, 21], [8, 15, 8, 1]], ![[0, 1], [17, 0, 20, 15, 17], [3, 1, 8, 10, 15], [3, 7, 1, 15, 17], [13, 14, 12, 9, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 4, 21, 1], [], [], []]
 b := ![[], [8, 5, 7, 5, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [14, 20, 2, 21, 17, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![762939670, -1089373495, 4421560710, -2782049985, 3777597740]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33171290, -47364065, 192241770, -120958695, 164243380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB853I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB853I0 : PrimesBelowBoundCertificateInterval O 1 23 853 where
  m := 9
  g := ![5, 5, 5, 2, 2, 2, 3, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB853I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![121, 1331]
    · exact ![28561, 13]
    · exact ![4913, 17, 17]
    · exact ![6859, 19, 19]
    · exact ![6436343]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N0, I13N1, I17N1, I17N2, I19N1, I19N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N0], [I13N1], [I17N1, I17N2], [I19N1, I19N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
