
import IdealArithmetic.Examples.NF5_1_158203125_7.RI5_1_158203125_7
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [16, 11, 13, 14, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 1, 13, 9, 18], [5, 9, 14, 11, 23], [19, 7, 23, 5, 24], [16, 11, 8, 4, 22], [0, 1]]
 g := ![![[22, 13, 22, 26, 1], [3, 13, 9, 5], [6, 7, 1], []], ![[7, 19, 4, 21, 11, 6, 28, 27], [21, 18, 11, 20], [12, 1, 2, 20, 21, 7, 12, 14], [8, 23, 7, 18, 1, 22, 11, 3]], ![[21, 15, 7, 6, 4, 20, 17, 16], [8, 27, 12, 5], [3, 15, 13, 23, 25, 5, 18, 25], [26, 12, 6, 14, 6, 3, 24, 16]], ![[25, 5, 27, 3, 20, 23, 28, 20], [14, 15, 11, 22], [15, 24, 4, 19, 20, 21, 24, 20], [26, 14, 24, 18, 9, 6, 22, 20]], ![[16, 24, 7, 1, 0, 1, 13, 6], [3, 5, 17, 6], [2, 6, 8, 18, 21, 22], [8, 16, 20, 1, 4, 27, 14, 5]]]
 h' := ![![[25, 1, 13, 9, 18], [4, 5, 13, 5, 28], [20, 25, 3, 17, 18], [0, 0, 0, 1], [0, 1]], ![[5, 9, 14, 11, 23], [6, 18, 12, 14, 25], [20, 4, 11, 26, 7], [11, 27, 27, 12, 2], [25, 1, 13, 9, 18]], ![[19, 7, 23, 5, 24], [10, 1, 27, 25, 23], [15, 28, 10, 24, 11], [28, 23, 17, 0, 22], [5, 9, 14, 11, 23]], ![[16, 11, 8, 4, 22], [17, 14, 10, 26, 24], [3, 10, 19, 27, 14], [5, 24, 1, 17, 5], [19, 7, 23, 5, 24]], ![[0, 1], [4, 20, 25, 17, 16], [20, 20, 15, 22, 8], [24, 13, 13, 28], [16, 11, 8, 4, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 8, 3, 4], [], [], []]
 b := ![[], [12, 1, 10, 16, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [16, 11, 13, 14, 22, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6049408935944, -3196186172497, -983859938968, -2959690724621, -1154052637747]
  a := ![0, -5, -8, -1, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-208600308136, -110213316293, -33926204792, -102058300849, -39794918543]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85954, -2184, 4406, -37046, 15123]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-85954, -2184, 4406, -37046, 15123]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![1, 6, 7, 1, 0], ![29, 14, 4, 0, 1]] where
  M :=![![![-85954, -2184, 4406, -37046, 15123], ![453690, -3711, -8774, 173260, -74092], ![-1338225, 32841, 5063, -479025, 210306], ![812715, -40693, 16646, 260566, -119912], ![-1798680, 102877, -49016, -557945, 260566]]]
  hmulB := by decide  
  f := ![![![20180576, 10213433, 3205260, 9709651, 3614290]], ![![108428700, 54875979, 17221606, 52169200, 19419302]], ![![237075180, 119984211, 37654373, 114065925, 42459549]], ![![83518706, 42268981, 13265179, 40184042, 14957984]], ![![120864439, 61169735, 19196762, 58152509, 21646510]]]
  g := ![![![-15725, 270, 6556, -37046, 15123], ![78358, -193, -29846, 173260, -74092], ![-224454, -1203, 81194, -479025, 210306], ![129987, 2409, -42828, 260566, -119912], ![-283779, -6367, 90785, -557945, 260566]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [11, 24, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 25], [2, 5], [0, 1]]
 g := ![![[13, 2, 18], [26, 21, 20], [20, 26, 10], [1]], ![[25, 0, 28], [27, 1, 7], [5, 16, 19], [1]], ![[27, 29, 16], [24, 9, 4], [19, 20, 2], [1]]]
 h' := ![![[12, 25], [24, 22, 7], [28, 6, 12], [20, 7, 14], [0, 1]], ![[2, 5], [25, 7, 4], [30, 3, 29], [12, 19, 8], [12, 25]], ![[0, 1], [3, 2, 20], [26, 22, 21], [28, 5, 9], [2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9], []]
 b := ![[], [28, 19, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [11, 24, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5633600572, -4384506788, -1213192678, -3210534768, -1857496393]
  a := ![3, -63, -61, -1, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1659494503, 1318827462, 925501170, -3210534768, -1857496393]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163454, 17154, -20018, -16538, 3937]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![163454, 17154, -20018, -16538, 3937]] 
 ![![31, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![163454, 17154, -20018, -16538, 3937], ![118110, 160257, 54326, -60720, -33076], ![-555195, 30691, 105931, 795, -44182], ![-423375, -164675, -9454, 42014, 4712], ![70680, -291699, -159948, -75, 42014]]]
  hmulB := by decide  
  f := ![![![282317984, -11440079, 3219856, 94458353, -42669254]], ![![13349364, -150617, -218738, 5037318, -2164478]], ![![203128040, -9943479, 3944191, 65458505, -30056263]], ![![-58823250, 3955079, -2164478, -17382856, 8299195]], ![![124487925, -8850576, 5037318, 36084780, -17382856]]]
  g := ![![![8410, 17154, -20018, -16538, 3937], ![-44732, 160257, 54326, -60720, -33076], ![-58021, 30691, 105931, 795, -44182], ![21265, -164675, -9454, 42014, 4712], ![110334, -291699, -159948, -75, 42014]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-296, -114, -124, -48, -101]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-296, -114, -124, -48, -101]] 
 ![![31, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-296, -114, -124, -48, -101], ![-3030, -1163, -104, -1630, -96], ![75, -1859, -1059, 75, -1582], ![-8265, -2269, -702, -3556, -248], ![-3720, -6589, -1918, -2995, -3556]]]
  hmulB := by decide  
  f := ![![![-422636, -45585, 50454, 37633, -11836]], ![![-297756, -44638, 29610, 29813, -5590]], ![![-189622, -29224, 18479, 19196, -3385]], ![![-363724, -30972, 47336, 30211, -11999]], ![![-300201, -11401, 45782, 21203, -13012]]]
  g := ![![![249, -114, -124, -48, -101], ![2337, -1163, -104, -1630, -96], ![2844, -1859, -1059, 75, -1582], ![5150, -2269, -702, -3556, -248], ![10606, -6589, -1918, -2995, -3556]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-85954, -2184, 4406, -37046, 15123]] ![![163454, 17154, -20018, -16538, 3937]]
  ![![-422636, -45585, 50454, 37633, -11836]] where
 M := ![![![-422636, -45585, 50454, 37633, -11836]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-422636, -45585, 50454, 37633, -11836]] ![![-296, -114, -124, -48, -101]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8396, -4262, -1334, -4046, -1509]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-8396, -4262, -1334, -4046, -1509]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![5, 13, 9, 3, 1]] where
  M :=![![![-8396, -4262, -1334, -4046, -1509], ![-45270, -22871, -7190, -21760, -8092], ![-98745, -50055, -15681, -47555, -17714], ![-107925, -54609, -17146, -51916, -19328], ![-289920, -146733, -46036, -139505, -51916]]]
  hmulB := by decide  
  f := ![![![148, 53, 0, -23, -4]], ![![-120, 181, 106, -40, -46]], ![![-630, -69, 75, 55, -17]], ![![-180, -213, -70, 68, 37]], ![![-175, 32, 45, 2, -16]]]
  g := ![![![-23, 415, 331, 13, -1509], ![-130, 2225, 1774, 68, -8092], ![-275, 4871, 3885, 151, -17714], ![-305, 5315, 4238, 164, -19328], ![-820, 14275, 11384, 439, -51916]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [27, 9, 17, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 7, 2, 36], [20, 22, 24, 27], [4, 7, 11, 11], [0, 1]]
 g := ![![[9, 15, 35, 21], [27, 27, 9], [21, 5, 36, 9], [1], []], ![[14, 30, 11, 14, 28, 7], [10, 23, 21], [25, 15, 24, 21, 20, 33], [7, 9, 33], [7, 36, 1]], ![[11, 34, 10, 18, 25, 1], [4, 1, 4], [36, 31, 15, 21, 10, 26], [11, 30, 28], [5, 5, 26]], ![[26, 18, 5, 7, 11, 21], [20, 15, 28], [19, 19, 34, 18, 27, 9], [9, 31, 12], [33, 13, 10]]]
 h' := ![![[16, 7, 2, 36], [7, 1, 21, 24], [25, 35, 0, 3], [10, 28, 20, 3], [0, 0, 1], [0, 1]], ![[20, 22, 24, 27], [23, 11, 30, 20], [16, 11, 7, 13], [8, 22, 31, 2], [30, 3, 13, 25], [16, 7, 2, 36]], ![[4, 7, 11, 11], [19, 13, 29, 23], [33, 9, 25, 2], [35, 17, 35, 8], [6, 34, 20, 19], [20, 22, 24, 27]], ![[0, 1], [3, 12, 31, 7], [5, 19, 5, 19], [0, 7, 25, 24], [13, 0, 3, 30], [4, 7, 11, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 18, 31], []]
 b := ![[], [], [12, 1, 14, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [27, 9, 17, 34, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3565718518, 1996047346, 600641208, 1784141186, 740543691]
  a := ![1, -5, -6, -1, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3702701, -206243801, -163898703, -11824051, 740543691]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-148, -53, 0, 23, 4]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-148, -53, 0, 23, 4]] 
 ![![37, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![-148, -53, 0, 23, 4], ![120, -181, -106, 40, 46], ![630, 69, -75, -55, 17], ![180, 213, 70, -68, -37], ![-555, 174, 178, -10, -68]]]
  hmulB := by decide  
  f := ![![![8396, 4262, 1334, 4046, 1509]], ![![8258, 4189, 1312, 3978, 1483]], ![![7661, 3887, 1217, 3691, 1376]], ![![5413, 2743, 860, 2606, 971]], ![![15324, 7767, 2434, 7379, 2749]]]
  g := ![![![30, -53, 0, 23, 4], ![165, -181, -106, 40, 46], ![5, 69, -75, -55, 17], ![-162, 213, 70, -68, -37], ![-203, 174, 178, -10, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-8396, -4262, -1334, -4046, -1509]] ![![-148, -53, 0, 23, 4]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [38, 38, 27, 37, 34, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 15, 37, 22, 29], [38, 28, 36, 29, 22], [15, 39, 23, 18, 12], [17, 40, 27, 13, 19], [0, 1]]
 g := ![![[20, 14, 23, 7, 16], [2, 36], [38, 3, 30, 8], [1], []], ![[9, 1, 29, 7, 11, 20, 10, 11], [23, 13, 6, 40], [34, 12, 14, 33], [7, 35, 26, 32, 0, 30, 5, 34], [39, 6, 29, 21]], ![[4, 12, 25, 19, 9, 14, 23, 7], [16, 5, 12, 23], [18, 3, 37, 23], [15, 33, 2, 18, 16, 24, 13, 19], [36, 27, 31, 33]], ![[29, 22, 21, 22, 1, 25, 29, 26], [23, 35, 23, 36], [2, 33, 34, 1], [35, 35, 33, 23, 16, 21, 9, 14], [23, 11, 5, 21]], ![[40, 24, 34, 14, 22, 7, 24, 29], [3, 40, 0, 39], [39, 36, 8, 9], [17, 4, 17, 34, 31, 28], [9, 6, 28, 33]]]
 h' := ![![[19, 15, 37, 22, 29], [6, 32, 9, 8, 37], [0, 18, 27, 6], [3, 3, 14, 4, 7], [0, 0, 1], [0, 1]], ![[38, 28, 36, 29, 22], [26, 27, 11, 19, 8], [11, 28, 11, 38, 32], [14, 40, 4, 37, 22], [27, 8, 27, 40, 2], [19, 15, 37, 22, 29]], ![[15, 39, 23, 18, 12], [32, 33, 18, 11, 27], [5, 38, 39, 17, 33], [19, 22, 40, 23, 8], [35, 21, 16, 14, 32], [38, 28, 36, 29, 22]], ![[17, 40, 27, 13, 19], [3, 24, 30, 11, 3], [37, 29, 25, 39, 6], [20, 35, 35, 34, 1], [7, 1, 39, 34, 7], [15, 39, 23, 18, 12]], ![[0, 1], [13, 7, 14, 33, 7], [39, 10, 21, 23, 11], [39, 23, 30, 25, 3], [29, 11, 40, 35], [17, 40, 27, 13, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 39, 26, 16], [], [], []]
 b := ![[], [35, 11, 23, 34, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [38, 38, 27, 37, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2607626983624585, 1386071366536000, 425543270214944, 1278800956685881, 501866564940457]
  a := ![1, 22, 26, -1, 51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![63600658137185, 33806618696000, 10379104151584, 31190267236241, 12240647925377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56025766, -25246969, -21520378, 3256795, 8437386]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![56025766, -25246969, -21520378, 3256795, 8437386]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![10, 15, 29, 23, 1]] where
  M :=![![![56025766, -25246969, -21520378, 3256795, 8437386], ![253121580, 29924971, -28973560, -23228030, 6513590], ![-28856940, 113871205, 58898531, -28251935, -26484825], ![-265928970, 24881693, 57137906, 9569706, -19203175], ![-288047625, -111393670, -3687260, 46828890, 9569706]]]
  hmulB := by decide  
  f := ![![![763033198, -70323038, 46153804, 197667410, -100497643]], ![![-3014929290, 282529553, -186799880, -774207410, 395334820]], ![![7437486945, -705927475, 469329433, 1896778105, -971874820]], ![![-3137779815, 307971531, -207651038, -785381622, 406202350]], ![![2605060780, -243276464, 160602711, 670191508, -341908174]]]
  g := ![![![-659258, -3530413, -6190804, -4437281, 8437386], ![4371760, -1576253, -5066690, -4024200, 6513590], ![5488170, 11887060, 19231592, 13509280, -26484825], ![-1718540, 7277426, 14279767, 10494017, -19203175], ![-8924295, -5928820, -6539738, -4029636, 9569706]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [15, 14, 2, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 24, 29, 12], [17, 27, 4, 21], [42, 34, 10, 10], [0, 1]]
 g := ![![[23, 10, 35, 10], [16, 37, 0, 23], [27, 41, 21], [15, 1], []], ![[23, 2, 24, 39, 6, 37], [19, 32, 34, 37, 8, 19], [27, 7, 41], [1, 30, 3, 25, 24, 42], [23, 18, 15]], ![[39, 8, 36, 0, 42, 11], [1, 5, 19, 36, 1, 11], [8, 32, 36], [18, 29, 5, 30, 6, 16], [17, 32, 11]], ![[19, 16, 27, 6, 19, 14], [0, 13, 42, 34, 40, 16], [0, 31, 23], [9, 39, 16, 6, 11, 9], [22, 23, 14]]]
 h' := ![![[42, 24, 29, 12], [18, 11, 32, 15], [39, 24, 37, 18], [33, 33, 42, 8], [0, 0, 1], [0, 1]], ![[17, 27, 4, 21], [38, 8, 2, 35], [35, 21, 13, 27], [28, 9, 24, 16], [0, 5, 38, 5], [42, 24, 29, 12]], ![[42, 34, 10, 10], [2, 34, 42, 8], [1, 18, 12, 35], [32, 27, 28, 37], [34, 28, 3, 21], [17, 27, 4, 21]], ![[0, 1], [39, 33, 10, 28], [41, 23, 24, 6], [27, 17, 35, 25], [15, 10, 1, 17], [42, 34, 10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 7, 4], []]
 b := ![[], [], [14, 35, 1, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [15, 14, 2, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2558961696, 1795283784, 499547376, 1405901760, 727442589]
  a := ![-1, -2, -6, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-109661958, -212008257, -478983435, -356401809, 727442589]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![763033198, -70323038, 46153804, 197667410, -100497643]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![763033198, -70323038, 46153804, 197667410, -100497643]] 
 ![![43, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![763033198, -70323038, 46153804, 197667410, -100497643], ![-3014929290, 282529553, -186799880, -774207410, 395334820], ![7437486945, -705927475, 469329433, 1896778105, -971874820], ![-3137779815, 307971531, -207651038, -785381622, 406202350], ![6093035250, -607049305, 411797050, 1511884155, -785381622]]]
  hmulB := by decide  
  f := ![![![56025766, -25246969, -21520378, 3256795, 8437386]], ![![58003540, -22789623, -20692760, 2489390, 8000210]], ![![51445900, -20837385, -18649223, 2372555, 7232805]], ![![14662402, -8815577, -6678794, 1434382, 2692907]], ![![24571413, -16681882, -12097124, 2906790, 4931790]]]
  g := ![![![22769010, -70323038, 46153804, 197667410, -100497643], ![-91740310, 282529553, -186799880, -774207410, 395334820], ![229719875, -705927475, 469329433, 1896778105, -971874820], ![-100775581, 307971531, -207651038, -785381622, 406202350], ![199119486, -607049305, 411797050, 1511884155, -785381622]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![56025766, -25246969, -21520378, 3256795, 8437386]] ![![763033198, -70323038, 46153804, 197667410, -100497643]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163411, -4642, 8842, -71148, 28936]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-163411, -4642, 8842, -71148, 28936]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![23, 14, 29, 17, 1]] where
  M :=![![![-163411, -4642, 8842, -71148, 28936], ![868080, -5689, -18126, 333570, -142296], ![-2568480, 60174, 12437, -923580, 404718], ![1567380, -77658, 31320, 503729, -231570], ![-3473550, 197256, -93318, -1079550, 503729]]]
  hmulB := by decide  
  f := ![![![-1277, 302, 358, -24, -140]], ![![-4200, -959, 246, 390, -48]], ![![1380, -1974, -1205, 180, 414]], ![![4440, -198, -888, -497, 174]], ![![637, -1392, -811, 7, 225]]]
  g := ![![![-17637, -8718, -17666, -11980, 28936], ![88104, 42265, 87414, 58566, -142296], ![-252702, -119274, -249455, -166038, 404718], ![146670, 67326, 143550, 94477, -231570], ![-320411, -145850, -312797, -205169, 503729]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [40, 10, 19, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 27, 44, 17], [39, 28, 12, 43], [0, 38, 38, 34], [0, 1]]
 g := ![![[14, 36, 35, 24], [13, 7], [3, 38, 38, 9], [43, 1], []], ![[18, 2, 6, 42, 28, 37], [4, 10, 45, 34, 30, 16], [17, 28, 5, 25, 8, 4], [19, 19, 9, 8, 32, 18], [45, 11, 7]], ![[16, 43, 23, 10, 8, 13], [39, 0, 14, 38, 17, 29], [1, 32, 36, 16, 5, 29], [7, 13, 6, 21, 19, 39], [21, 28, 16]], ![[0, 7, 8, 43, 19, 24], [38, 14, 3, 37, 4, 25], [3, 9, 4, 21, 23, 6], [4, 42, 11, 3, 39, 14], [0, 28, 28]]]
 h' := ![![[4, 27, 44, 17], [44, 31, 35, 20], [21, 33, 17], [19, 0, 19, 44], [0, 0, 1], [0, 1]], ![[39, 28, 12, 43], [32, 40, 26, 43], [46, 8, 27, 24], [8, 30, 26, 12], [2, 31, 24, 32], [4, 27, 44, 17]], ![[0, 38, 38, 34], [22, 44, 9, 28], [7, 26, 22, 34], [0, 45, 45, 13], [23, 8, 25, 7], [39, 28, 12, 43]], ![[0, 1], [31, 26, 24, 3], [21, 27, 28, 36], [28, 19, 4, 25], [0, 8, 44, 8], [0, 38, 38, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 42, 19], []]
 b := ![[], [], [7, 43, 32, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [40, 10, 19, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1285938040, 651073740, 204420760, 619056260, 230396460]
  a := ![0, -6, -2, -10, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-85386820, -54776100, -137810140, -70163480, 230396460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1277, 302, 358, -24, -140]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-1277, 302, 358, -24, -140]] 
 ![![47, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-1277, 302, 358, -24, -140], ![-4200, -959, 246, 390, -48], ![1380, -1974, -1205, 180, 414], ![4440, -198, -888, -497, 174], ![2610, 1668, 246, -1350, -497]]]
  hmulB := by decide  
  f := ![![![-163411, -4642, 8842, -71148, 28936]], ![![-26729, -1405, 2060, -12582, 4976]], ![![-65079, 984, 829, -24192, 10458]], ![![-119632, -5998, 8944, -55889, 22162]], ![![-223409, -50, 6104, -88062, 37191]]]
  g := ![![![17, 302, 358, -24, -140], ![-161, -959, 246, 390, -48], ![105, -1974, -1205, 180, 414], ![512, -198, -888, -497, 174], ![1297, 1668, 246, -1350, -497]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-163411, -4642, 8842, -71148, 28936]] ![![-1277, 302, 358, -24, -140]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97706, 49450, 15516, 46988, 17491]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![97706, 49450, 15516, 46988, 17491]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![27, 1, 40, 30, 1]] where
  M :=![![![97706, 49450, 15516, 46988, 17491], ![524730, 265643, 83384, 252490, 93976], ![1147275, 580689, 182259, 552095, 205502], ![1252575, 633879, 198922, 602686, 224348], ![3365220, 1703019, 534418, 1619045, 602686]]]
  hmulB := by decide  
  f := ![![![3868, -323, 202, 1051, -522]], ![![-15660, 1339, -848, -4210, 2102]], ![![39360, -3423, 2187, 10495, -5261]], ![![-17430, 1581, -1030, -4552, 2305]], ![![22167, -1888, 1194, 5969, -2978]]]
  g := ![![![-7067, 603, -12908, -9014, 17491], ![-37974, 3239, -69352, -48430, 93976], ![-83043, 7079, -151657, -105905, 205502], ![-90657, 7727, -165566, -115618, 224348], ![-243534, 20761, -444774, -310595, 602686]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [11, 24, 7, 36, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 41, 22], [47, 26, 1, 12], [36, 38, 30, 41], [0, 1]]
 g := ![![[6, 31, 48, 15], [3, 33, 43], [12, 1, 7, 10], [17, 17, 1], []], ![[44, 24, 32, 5, 14], [52, 21, 36], [20, 31, 44, 30, 35], [30, 21, 15], [39, 34, 48]], ![[26, 10, 6, 8, 5, 8], [18, 12, 9], [2, 37, 18, 3, 48, 30], [7], [27, 48, 22, 23, 22, 32]], ![[40, 23, 19, 20, 11, 8], [9, 2, 42], [13, 48, 23, 32, 34, 35], [48, 41, 38], [36, 27, 4, 7, 14, 21]]]
 h' := ![![[40, 41, 22], [7, 50, 7, 42], [27, 8, 10, 34], [25, 41, 45, 40], [0, 0, 0, 1], [0, 1]], ![[47, 26, 1, 12], [2, 16, 51, 37], [16, 2, 36, 47], [34, 32, 14, 2], [24, 26, 52, 11], [40, 41, 22]], ![[36, 38, 30, 41], [21, 5, 50, 6], [31, 22, 50, 50], [0, 41, 13, 20], [17, 42, 31], [47, 26, 1, 12]], ![[0, 1], [36, 35, 51, 21], [33, 21, 10, 28], [30, 45, 34, 44], [44, 38, 23, 41], [36, 38, 30, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [28, 37, 49], []]
 b := ![[], [], [7, 50, 3, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [11, 24, 7, 36, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2982730939, 1797391040, 524645920, 1539611136, 686678308]
  a := ![13, -3, -6, 1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-293539309, 20956844, -508348800, -359636568, 686678308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3868, 323, -202, -1051, 522]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-3868, 323, -202, -1051, 522]] 
 ![![53, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-3868, 323, -202, -1051, 522], ![15660, -1339, 848, 4210, -2102], ![-39360, 3423, -2187, -10495, 5261], ![17430, -1581, 1030, 4552, -2305], ![-34575, 3192, -2096, -8950, 4552]]]
  hmulB := by decide  
  f := ![![![-97706, -49450, -15516, -46988, -17491]], ![![-94702, -47931, -15040, -45546, -16954]], ![![-80639, -40813, -12807, -38787, -14438]], ![![-25477, -12893, -4046, -12258, -4563]], ![![-118800, -60123, -18866, -57145, -21272]]]
  g := ![![![-507, 323, -202, -1051, 522], ![2056, -1339, 848, 4210, -2102], ![-5173, 3423, -2187, -10495, 5261], ![2298, -1581, 1030, 4552, -2305], ![-4565, 3192, -2096, -8950, 4552]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![97706, 49450, 15516, 46988, 17491]] ![![-3868, 323, -202, -1051, 522]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86, 10, -4, -22, 13]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-86, 10, -4, -22, 13]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![13, 22, 10, 1, 0], ![29, 38, 3, 0, 1]] where
  M :=![![![-86, 10, -4, -22, 13], ![390, -19, 24, 110, -44], ![-855, 109, -43, -215, 132], ![465, -5, 34, 134, -42], ![-630, 159, -22, -125, 134]]]
  hmulB := by decide  
  f := ![![![-34, -1, 6, 3, -2]], ![![-60, -33, -8, 10, 6]], ![![120, -23, -25, 5, 7]], ![![-8, -16, -6, 5, 3]], ![![-49, -22, -3, 8, 3]]]
  g := ![![![-3, 0, 3, -22, 13], ![4, -13, -16, 110, -44], ![-32, -3, 29, -215, 132], ![-1, -23, -20, 134, -42], ![-49, -37, 14, -125, 134]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [24, 4, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 25, 18], [17, 33, 41], [0, 1]]
 g := ![![[56, 36, 1], [3, 25, 19], [35, 20], [37, 33, 15], [1]], ![[15, 51, 15, 11], [1, 44, 58, 8], [], [8, 23, 52, 14], [58, 27, 17, 50]], ![[55, 5, 51, 25], [15, 48, 45, 22], [0, 20], [31, 9, 28, 7], [30, 51, 14, 9]]]
 h' := ![![[13, 25, 18], [46, 3, 1], [54, 30, 45], [56, 49, 43], [35, 55, 30], [0, 1]], ![[17, 33, 41], [18, 29, 28], [25, 37, 19], [54, 14], [38, 54, 33], [13, 25, 18]], ![[0, 1], [53, 27, 30], [0, 51, 54], [0, 55, 16], [4, 9, 55], [17, 33, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 14], []]
 b := ![[], [44, 19, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [24, 4, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5262, -3036, -888, -2694, -1110]
  a := ![-1, -2, 0, -1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1050, 1668, 498, -2694, -1110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13502569, 1566312, -1122682, -3027126, 1657272]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-13502569, 1566312, -1122682, -3027126, 1657272]] 
 ![![59, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-13502569, 1566312, -1122682, -3027126, 1657272], ![49718160, -5895261, 4255306, 10959310, -6054252], ![-115672860, 13978756, -10150567, -25112650, 13986436], ![40896780, -5258756, 3889380, 8416051, -4826072], ![-72391080, 9643212, -7203446, -14406910, 8416051]]]
  hmulB := by decide  
  f := ![![![711010669, 9146552, -116896550, -45512986, 34737744]], ![![282785882, 14597915, -41297194, -20989678, 11410244]], ![![474169362, 13777052, -74318507, -32375398, 21481236]], ![![437046069, -1606228, -75280762, -26071295, 22939368]], ![![517851173, -11699348, -93842964, -28310232, 29330899]]]
  g := ![![![779431, 1566312, -1122682, -3027126, 1657272], ![-2820156, -5895261, 4255306, 10959310, -6054252], ![6459236, 13978756, -10150567, -25112650, 13986436], ![-2160499, -5258756, 3889380, 8416051, -4826072], ![3694615, 9643212, -7203446, -14406910, 8416051]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-717387194, 40911649, 141712544, 32708799, -46055242]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-717387194, 40911649, 141712544, 32708799, -46055242]] 
 ![![59, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-717387194, 40911649, 141712544, 32708799, -46055242], ![-1381657260, -623326667, -59889246, 248010300, 65417598], ![1672092600, -587173881, -563437421, 53359725, 215301501], ![2178890430, 338806167, -210913854, -221366594, 38237151], ![573557265, 1143527322, 444263094, -336098880, -221366594]]]
  hmulB := by decide  
  f := ![![![280280774, -8516078, 494822, 97933584, -43431409]], ![![196440226, -5697327, 88726, 69035676, -30541994]], ![![250859485, -8813107, 1574867, 85911555, -38424236]], ![![19381691, 503797, -1004716, 8370682, -3414775]], ![![269761002, -10844001, 2992272, 90386037, -40805396]]]
  g := ![![![-113445787, 40911649, 141712544, 32708799, -46055242], ![410360794, -623326667, -59889246, 248010300, 65417598], ![704914711, -587173881, -563437421, 53359725, 215301501], ![-70179100, 338806167, -210913854, -221366594, 38237151], ![-962792181, 1143527322, 444263094, -336098880, -221366594]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-86, 10, -4, -22, 13]] ![![-13502569, 1566312, -1122682, -3027126, 1657272]]
  ![![280280774, -8516078, 494822, 97933584, -43431409]] where
 M := ![![![280280774, -8516078, 494822, 97933584, -43431409]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![280280774, -8516078, 494822, 97933584, -43431409]] ![![-717387194, 40911649, 141712544, 32708799, -46055242]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10426, -1517, 1160, 1887, -1164]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![10426, -1517, 1160, 1887, -1164]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![25, 59, 1, 0, 0], ![25, 3, 0, 1, 0], ![47, 20, 0, 0, 1]] where
  M :=![![![10426, -1517, 1160, 1887, -1164], ![-34920, 5409, -4194, -5840, 3774], ![74070, -12219, 9603, 11305, -7727], ![-17580, 3877, -3210, -1254, 1467], ![22005, -6394, 5482, -690, -1254]]]
  hmulB := by decide  
  f := ![![![907816, 459444, 144186, 436788, 162589]], ![![4877670, 2468577, 774702, 2346820, 873576]], ![![5264635, 2664420, 836163, 2533005, 942881]], ![![802795, 406294, 127506, 386256, 143779]], ![![2811422, 1422857, 446530, 1352681, 503519]]]
  g := ![![![-181, -858, 1160, 1887, -1164], ![632, 3195, -4194, -5840, 3774], ![-1401, -7511, 9603, 11305, -7727], ![411, 2749, -3210, -1254, 1467], ![-637, -4962, 5482, -690, -1254]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [30, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 60], [0, 1]]
 g := ![![[25, 4], [1], [20, 25], [33, 60], [43, 1]], ![[14, 57], [1], [58, 36], [51, 1], [25, 60]]]
 h' := ![![[43, 60], [9, 2], [10, 1], [47, 5], [52, 50], [0, 1]], ![[0, 1], [34, 59], [53, 60], [18, 56], [6, 11], [43, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [34, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [30, 18, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8547, 8666, 2896, -1161, 6872]
  a := ![3, 3, 10, -4, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6146, -4855, 2896, -1161, 6872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50284456, -29717353, -22660564, 4782427, 9121796]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![50284456, -29717353, -22660564, 4782427, 9121796]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![28, 14, 1, 0, 0], ![44, 43, 0, 1, 0], ![16, 21, 0, 0, 1]] where
  M :=![![![50284456, -29717353, -22660564, 4782427, 9121796], ![273653880, 20854955, -36774142, -22084860, 9564854], ![6645870, 123964933, 57629097, -33068655, -26867287], ![-269336100, 38757517, 64295630, 6114736, -22426861], ![-336402915, -107060814, 6609702, 48604770, 6114736]]]
  hmulB := by decide  
  f := ![![![3343636, -276210, 193490, 891758, -435043]], ![![-13051290, 1279191, -745910, -3382980, 1783516]], ![![-915047, 120689, -49179, -223741, 139562]], ![![-7014061, 727970, -399792, -1797592, 975060]], ![![-3141614, 333300, -173782, -806467, 443784]]]
  g := ![![![5383684, -1797894, -22660564, 4782427, 9121796], ![34787312, 21057049, -36774142, -22084860, 9564854], ![4556206, 21365947, 57629097, -33068655, -26867287], ![-32456268, -10710670, 64295630, 6114736, -22426861], ![-45211807, -39639528, 6609702, 48604770, 6114736]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [29, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 60], [0, 1]]
 g := ![![[45, 5], [25], [39, 52], [48, 4], [37, 1]], ![[47, 56], [25], [11, 9], [13, 57], [13, 60]]]
 h' := ![![[37, 60], [59, 35], [28, 56], [11, 28], [25, 59], [0, 1]], ![[0, 1], [12, 26], [26, 5], [10, 33], [12, 2], [37, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [27, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [29, 24, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-996, 3900, 1208, 749, 2657]
  a := ![1, 2, 4, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1808, -1656, 1208, 749, 2657]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-104, 42, 38, -4, -15]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-104, 42, 38, -4, -15]] 
 ![![61, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![-104, 42, 38, -4, -15], ![-450, -61, 46, 40, -8], ![105, -199, -107, 55, 44], ![465, -33, -98, -24, 34], ![510, 203, 16, -75, -24]]]
  hmulB := by decide  
  f := ![![![37186, 18837, 5908, 17899, 6668]], ![![27054, 13702, 4298, 13021, 4850]], ![![15088, 7642, 2397, 7262, 2705]], ![![27332, 13841, 4342, 13154, 4899]], ![![49667, 25151, 7890, 23903, 8902]]]
  g := ![![![-23, 42, 38, -4, -15], ![7, -61, 46, 40, -8], ![89, -199, -107, 55, 44], ![36, -33, -98, -24, 34], ![-67, 203, 16, -75, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![10426, -1517, 1160, 1887, -1164]] ![![50284456, -29717353, -22660564, 4782427, 9121796]]
  ![![177783856, 83455242, 9246352, -32768726, -9130753]] where
 M := ![![![177783856, 83455242, 9246352, -32768726, -9130753]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![177783856, 83455242, 9246352, -32768726, -9130753]] ![![-104, 42, 38, -4, -15]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-74967654584, -236046759, 12670611096, 4606879515, -3822558900]]]
 hmul := by decide  
 g := ![![![![-1228977944, -3869619, 207714936, 75522615, -62664900]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB784I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB784I1 : PrimesBelowBoundCertificateInterval O 23 61 784 where
  m := 9
  g := ![1, 3, 2, 1, 2, 2, 2, 3, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB784I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![29791, 31, 31]
    · exact ![1874161, 37]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![4879681, 47]
    · exact ![7890481, 53]
    · exact ![205379, 59, 59]
    · exact ![3721, 3721, 61]
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
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I31N1, I31N2, I37N1, I43N1, I47N1, I53N1, I59N1, I59N2, I61N2]
  Il := ![[], [I31N1, I31N2], [I37N1], [], [I43N1], [I47N1], [I53N1], [I59N1, I59N2], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
