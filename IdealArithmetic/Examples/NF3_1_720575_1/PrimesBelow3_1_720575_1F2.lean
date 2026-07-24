
import IdealArithmetic.Examples.NF3_1_720575_1.RI3_1_720575_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [37, 26, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 24, 23], [56, 58, 60], [0, 1]]
 g := ![![[54, 72, 7], [45, 4, 61], [], [2, 26], [67, 50, 1], []], ![[35, 82, 53, 51], [72, 0, 24, 44], [59, 40], [16, 44], [6, 52, 34, 16], [81, 31]], ![[20, 58, 28, 22], [17, 19, 10, 34], [30, 40], [9, 41], [63, 66, 18, 32], [44, 31]]]
 h' := ![![[77, 24, 23], [78, 38, 16], [51, 46, 12], [47, 57], [11, 60, 21], [0, 0, 1], [0, 1]], ![[56, 58, 60], [33, 32, 59], [16, 29, 11], [37, 40, 66], [52, 36, 25], [27, 28, 58], [77, 24, 23]], ![[0, 1], [23, 13, 8], [56, 8, 60], [2, 69, 17], [13, 70, 37], [14, 55, 24], [56, 58, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 66], []]
 b := ![[], [33, 36, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [37, 26, 33, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-323451, 57602, 1826]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3897, 694, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![232633758559, -6391603206, -7191749096]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![232633758559, -6391603206, -7191749096]] 
 ![![89, 0, 0], ![0, 89, 0], ![49, 20, 1]] where
  M :=![![![232633758559, -6391603206, -7191749096], ![1265747840896, 89598922529, -12783206412], ![492048243808, 511433459534, 95990525735]]]
  hmulB := by decide  
  f := ![![![170094462450276596807, -34433345710498264886, 8158181496476502704]], ![![-1435839943379864475904, 290666565172831883297, -68866691420996529772]], ![![-152853723492091117041, 30943189027559813660, -7331269934935413649]]]
  g := ![![![6573364767, 1544307626, -7191749096], ![21259830956, 3879360121, -12783206412], ![-47320084463, -15824461294, 95990525735]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [38, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 88], [0, 1]]
 g := ![![[30, 45], [34], [36], [28, 69], [61, 22], [1]], ![[83, 44], [34], [36], [44, 20], [79, 67], [1]]]
 h' := ![![[17, 88], [65, 32], [72, 37], [4, 6], [85, 43], [51, 17], [0, 1]], ![[0, 1], [75, 57], [78, 52], [17, 83], [15, 46], [73, 72], [17, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [43, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [38, 72, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33, -1185, 586]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-323, -145, 586]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-170094462450276596807, 34433345710498264886, -8158181496476502704]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-170094462450276596807, 34433345710498264886, -8158181496476502704]] 
 ![![89, 0, 0], ![49, 1, 0], ![21, 0, 1]] where
  M :=![![![-170094462450276596807, 34433345710498264886, -8158181496476502704], ![1435839943379864475904, -290666565172831883297, 68866691420996529772], ![-6778188816737626857888, 1372153540189399270786, -325099910883330148183]]]
  hmulB := by decide  
  f := ![![![-232633758559, 6391603206, 7191749096]], ![![-142301146183, 2512243085, 4103133844]], ![![-60419743523, -4238312272, 618384329]]]
  g := ![![![-18943894279086348533, 34433345710498264886, -8158181496476502704], ![159913495696715726205, -290666565172831883297, 68866691420996529772], ![-754905777050205146231, 1372153540189399270786, -325099910883330148183]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![232633758559, -6391603206, -7191749096]] ![![-170094462450276596807, 34433345710498264886, -8158181496476502704]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2319792122127, 459271526282, 155502336214]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-2319792122127, 459271526282, 155502336214]] 
 ![![97, 0, 0], ![0, 97, 0], ![79, 48, 1]] where
  M :=![![![-2319792122127, 459271526282, 155502336214], ![-27368411173664, 1094023792221, 918543052564], ![-67147583038800, -4958046587474, 634752265939]]]
  hmulB := by decide  
  f := ![![![-54109415755838646159215, 10953726488647626813322, -2595231073636396017482]], ![![456760668960005699076832, -92465079666282543678051, 21907452977295253626644]], ![![159728165658629230313679, -32334827769217441436108, 7660986411731615651613]]]
  g := ![![![-150561615289, -72214851670, 155502336214], ![-1030240333260, -443258172483, 918543052564], ![-1209206309773, -365218096418, 634752265939]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [7, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 96], [0, 1]]
 g := ![![[79, 1], [61], [43], [9], [66], [29, 1]], ![[11, 96], [61], [43], [9], [66], [58, 96]]]
 h' := ![![[29, 96], [25, 1], [89, 62], [83, 25], [7, 94], [88, 58], [0, 1]], ![[0, 1], [54, 96], [44, 35], [32, 72], [17, 3], [24, 39], [29, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [27, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [7, 68, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-161, -88, 79]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -40, 79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54109415755838646159215, 10953726488647626813322, -2595231073636396017482]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-54109415755838646159215, 10953726488647626813322, -2595231073636396017482]] 
 ![![97, 0, 0], ![1, 1, 0], ![96, 0, 1]] where
  M :=![![![-54109415755838646159215, 10953726488647626813322, -2595231073636396017482], ![456760668960005699076832, -92465079666282543678051, 21907452977295253626644], ![-2156236196481985168683088, 436501137764307758991534, -103418806154930170491373]]]
  hmulB := by decide  
  f := ![![![-2319792122127, 459271526282, 155502336214]], ![![-306063951503, 16013353799, 11072632874]], ![![-2988119863536, 403422885934, 160443057139]]]
  g := ![![![1897722070356780873255, 10953726488647626813322, -2595231073636396017482], ![-16019481826742846447453, -92465079666282543678051, 21907452977295253626644], ![75623382027082509685538, 436501137764307758991534, -103418806154930170491373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-2319792122127, 459271526282, 155502336214]] ![![-54109415755838646159215, 10953726488647626813322, -2595231073636396017482]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![3, 38, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![3, 38, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![3, 38, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![3, 38, 1], ![-176, 60, 76], ![-6600, 634, 22]]]
  hmulB := by decide  
  f := ![![![-2, -38, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -38, 101]], ![![0, 0, 1], ![-4, -28, 76], ![-66, -2, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [52, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 100], [0, 1]]
 g := ![![[53, 68], [70], [100, 84], [4], [58], [72, 1]], ![[0, 33], [70], [88, 17], [4], [58], [43, 100]]]
 h' := ![![[72, 100], [74, 13], [52, 75], [24, 36], [63, 99], [94, 82], [0, 1]], ![[0, 1], [0, 88], [99, 26], [91, 65], [20, 2], [39, 19], [72, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [70, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [52, 29, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1238, -1878, 328]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -142, 328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![25, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![25, 1, 0]] 
 ![![101, 0, 0], ![25, 1, 0], ![79, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![25, 1, 0], ![0, 26, 2], ![-176, 19, 25]]]
  hmulB := by decide  
  f := ![![![1976, 79, 0], ![-7979, 0, 0]], ![![450, 18, 0], ![-1817, 0, 0]], ![![1554, 49, -1], ![-6275, 51, 0]]]
  g := ![![![1, 0, 0], ![-25, 101, 0], ![-79, 0, 101]], ![![0, 1, 0], ![-8, 26, 2], ![-26, 19, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![3, 38, 1]] ![![101, 0, 0], ![25, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![2525, 101, 0]], ![![303, 3838, 101], ![-101, 1010, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![25, 1, 0]]], ![![![3, 38, 1]], ![![-1, 10, 1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![15, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![15, 1, 0]] 
 ![![103, 0, 0], ![15, 1, 0], ![86, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![15, 1, 0], ![0, 16, 2], ![-176, 19, 15]]]
  hmulB := by decide  
  f := ![![![676, 45, 0], ![-4635, 0, 0]], ![![90, 6, 0], ![-617, 0, 0]], ![![542, 28, -1], ![-3716, 52, 0]]]
  g := ![![![1, 0, 0], ![-15, 103, 0], ![-86, 0, 103]], ![![0, 1, 0], ![-4, 16, 2], ![-17, 19, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![37, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![37, 1, 0]] 
 ![![103, 0, 0], ![37, 1, 0], ![18, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![37, 1, 0], ![0, 38, 2], ![-176, 19, 37]]]
  hmulB := by decide  
  f := ![![![1222, 33, 0], ![-3399, 0, 0]], ![![444, 12, 0], ![-1235, 0, 0]], ![![192, -14, -1], ![-534, 52, 0]]]
  g := ![![![1, 0, 0], ![-37, 103, 0], ![-18, 0, 103]], ![![0, 1, 0], ![-14, 38, 2], ![-15, 19, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79074300321121101, 16007532994020166, -3792613142330708]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-79074300321121101, 16007532994020166, -3792613142330708]] 
 ![![103, 0, 0], ![50, 1, 0], ![64, 0, 1]] where
  M :=![![![-79074300321121101, 16007532994020166, -3792613142330708], ![667499913050204608, -135126417031384387, 32015065988040332], ![-3151075763472651520, 637893083411485458, -151133950025404553]]]
  hmulB := by decide  
  f := ![![![-2787421955, 578628466, 192520884]], ![![-1682085178, 294956569, 104692244]], ![![-2556230848, 301789562, 128075839]]]
  g := ![![![-6181783581679263, 16007532994020166, -3792613142330708], ![52183073217328570, -135126417031384387, 32015065988040332], ![-246341331382728476, 637893083411485458, -151133950025404553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![15, 1, 0]] ![![103, 0, 0], ![37, 1, 0]]
  ![![2787421955, -578628466, -192520884]] where
 M := ![![![10609, 0, 0], ![3811, 103, 0]], ![![1545, 103, 0], ![555, 53, 2]]]
 hmul := by decide  
 g := ![![![![8144652933075473403, -1648775898384077098, 390639153660062924]], ![![2258249198831276129, -457152303747361755, 108311620278195864]]], ![![![518614591766611907, -104986577878918103, 24874131146920288]], ![![143795075859288057, -29109387144085345, 6896793171633150]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![2787421955, -578628466, -192520884]] ![![-79074300321121101, 16007532994020166, -3792613142330708]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-15, 13, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-15, 13, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![92, 13, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-15, 13, 1], ![-176, 17, 26], ![-2200, 159, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -13, 107]], ![![-1, 0, 1], ![-24, -3, 26], ![-24, 1, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [12, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 106], [0, 1]]
 g := ![![[40, 9], [94, 75], [62], [36, 3], [75], [55, 1]], ![[0, 98], [46, 32], [62], [94, 104], [75], [3, 106]]]
 h' := ![![[55, 106], [49, 3], [21, 90], [103, 94], [66, 89], [89, 17], [0, 1]], ![[0, 1], [0, 104], [49, 17], [30, 13], [39, 18], [61, 90], [55, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [14, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [12, 52, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1308, -664, 23]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -9, 23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-26, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-26, 1, 0]] 
 ![![107, 0, 0], ![81, 1, 0], ![103, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-26, 1, 0], ![0, -25, 2], ![-176, 19, -26]]]
  hmulB := by decide  
  f := ![![![1977, -76, 0], ![8132, 0, 0]], ![![1483, -57, 0], ![6100, 0, 0]], ![![1889, -60, -1], ![7770, 54, 0]]]
  g := ![![![1, 0, 0], ![-81, 107, 0], ![-103, 0, 107]], ![![-1, 1, 0], ![17, -25, 2], ![9, 19, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-15, 13, 1]] ![![107, 0, 0], ![-26, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-2782, 107, 0]], ![![-1605, 1391, 107], ![214, -321, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-26, 1, 0]]], ![![![-15, 13, 1]], ![![2, -3, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![26, 5, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![26, 5, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![26, 5, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![26, 5, 1], ![-176, 50, 10], ![-792, 7, 45]]]
  hmulB := by decide  
  f := ![![![-25, -5, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -5, 109]], ![![0, 0, 1], ![-4, 0, 10], ![-18, -2, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [86, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 108], [0, 1]]
 g := ![![[38, 31], [74], [30, 74], [58, 106], [75], [2, 1]], ![[100, 78], [74], [69, 35], [52, 3], [75], [4, 108]]]
 h' := ![![[2, 108], [55, 85], [36, 40], [26, 69], [26, 18], [46, 27], [0, 1]], ![[0, 1], [7, 24], [7, 69], [55, 40], [62, 91], [100, 82], [2, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [25, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [86, 107, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108838, -20268, 11468]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3734, -712, 11468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-10, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-10, 1, 0]] 
 ![![109, 0, 0], ![99, 1, 0], ![64, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-10, 1, 0], ![0, -9, 2], ![-176, 19, -10]]]
  hmulB := by decide  
  f := ![![![271, -27, 0], ![2943, 0, 0]], ![![241, -24, 0], ![2617, 0, 0]], ![![156, -11, -1], ![1694, 55, 0]]]
  g := ![![![1, 0, 0], ![-99, 109, 0], ![-64, 0, 109]], ![![-1, 1, 0], ![7, -9, 2], ![-13, 19, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![26, 5, 1]] ![![109, 0, 0], ![-10, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1090, 109, 0]], ![![2834, 545, 109], ![-436, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-10, 1, 0]]], ![![![26, 5, 1]], ![![-4, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57183815199, 11576097478, -2742687424]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-57183815199, 11576097478, -2742687424]] 
 ![![113, 0, 0], ![7, 1, 0], ![85, 0, 1]] where
  M :=![![![-57183815199, 11576097478, -2742687424], ![482712986624, -97718778777, 23152194956], ![-2278749649440, 461302345394, -109294876255]]]
  hmulB := by decide  
  f := ![![![1392529, 540166, 79480]], ![![-37529, 63929, 14484]], ![![268053, 435248, 85473]]]
  g := ![![![839928615, 11576097478, -2742687424], ![-7090195869, -97718778777, 23152194956], ![33470782429, 461302345394, -109294876255]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2806042228200441566904323, 568045665508527837094830, -134585226671494811120214]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-2806042228200441566904323, 568045665508527837094830, -134585226671494811120214]] 
 ![![113, 0, 0], ![22, 1, 0], ![86, 0, 1]] where
  M :=![![![-2806042228200441566904323, 568045665508527837094830, -134585226671494811120214], ![23686999894183086757157664, -4795115869450315141093559, 1136091331017055674189660], ![-111819537076592442707268912, 22636367591753572283380602, -5363161534958842978188389]]]
  hmulB := by decide  
  f := ![![![-22392463511131, 3224339759958, 1244944643826]], ![![-6298623491666, 667445125669, 299446563576]], ![![-21094517973922, 2026553505654, 958643576023]]]
  g := ![![![-32997498899464603775683, 568045665508527837094830, -134585226671494811120214], ![278545969509940105140754, -4795115869450315141093559, 1136091331017055674189660], ![-1314935682200978201924254, 22636367591753572283380602, -5363161534958842978188389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1645435722941349755, -27210396647380876, -47055236700417250]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![1645435722941349755, -27210396647380876, -47055236700417250]] 
 ![![113, 0, 0], ![83, 1, 0], ![17, 0, 1]] where
  M :=![![![1645435722941349755, -27210396647380876, -47055236700417250], ![8281721659273436000, 724175828986041129, -54420793294761752], ![648168980302316176, 3623863293336481356, 751386225633422005]]]
  hmulB := by decide  
  f := ![![![-741349258051915151758509791953539357, 150076227803037883354799239571214620, -35557076417074641519026241182130002]], ![![-489149937777909917598298179505211383, 99021853322821671337903785394407245, -23460928203638225481146721583843902]], ![![-372967931016989323044368511962578605, 75502362173556922605726388040629792, -17888531053686745543747384730178933]]]
  g := ![![![41626882022841201, -27210396647380876, -47055236700417250], ![-450439988146522371, 724175828986041129, -54420793294761752], ![-2769080090286670889, 3623863293336481356, 751386225633422005]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-57183815199, 11576097478, -2742687424]] ![![-2806042228200441566904323, 568045665508527837094830, -134585226671494811120214]]
  ![![741349258051915151758509791953539357, -150076227803037883354799239571214620, 35557076417074641519026241182130002]] where
 M := ![![![741349258051915151758509791953539357, -150076227803037883354799239571214620, 35557076417074641519026241182130002]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![741349258051915151758509791953539357, -150076227803037883354799239571214620, 35557076417074641519026241182130002]] ![![1645435722941349755, -27210396647380876, -47055236700417250]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63604653060005, 2175944040980, -1135184060376]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![63604653060005, 2175944040980, -1135184060376]] 
 ![![127, 0, 0], ![0, 127, 0], ![103, 46, 1]] where
  M :=![![![63604653060005, 2175944040980, -1135184060376], ![199792394626176, 44212099953841, 4351888081960], ![-482862348525568, 141239134091708, 42036155912861]]]
  hmulB := by decide  
  f := ![![![9794093090823626161085523, -1982682966035523616425244, 469750677813413640912008]], ![![-82676119295160800800513408, 16736673003242961721988431, -3965365932071047232850488]], ![![-18929288484667171538115813, 3831980918466629587459302, -907898874733921908336787]]]
  g := ![![![1421485128179, 428302447388, -1135184060376], ![-1956315573352, -1228147652097, 4351888081960], ![-37894381161813, -14113575101574, 42036155912861]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [74, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 126], [0, 1]]
 g := ![![[86, 115], [104, 21], [21, 38], [19, 94], [85, 25], [113, 1]], ![[0, 12], [64, 106], [124, 89], [100, 33], [116, 102], [99, 126]]]
 h' := ![![[113, 126], [51, 49], [97, 23], [118, 61], [60, 27], [20, 122], [0, 1]], ![[0, 1], [0, 78], [29, 104], [26, 66], [63, 100], [90, 5], [113, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [23, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [74, 14, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-555, 16, 39]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -14, 39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9794093090823626161085523, 1982682966035523616425244, -469750677813413640912008]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-9794093090823626161085523, 1982682966035523616425244, -469750677813413640912008]] 
 ![![127, 0, 0], ![35, 1, 0], ![5, 0, 1]] where
  M :=![![![-9794093090823626161085523, 1982682966035523616425244, -469750677813413640912008], ![82676119295160800800513408, -16736673003242961721988431, 3965365932071047232850488], ![-390290261669832556891099648, 79009036002255349112336340, -18719355969278485338413675]]]
  hmulB := by decide  
  f := ![![![-63604653060005, -2175944040980, 1135184060376]], ![![-19102009856113, -947796388883, 278579165600]], ![![1297945537209, -1197786254304, -286301067803]]]
  g := ![![![-605033413488188067176449, 1982682966035523616425244, -469750677813413640912008], ![5107345234238655314219339, -16736673003242961721988431, 3965365932071047232850488], ![-24110312928365175977407899, 79009036002255349112336340, -18719355969278485338413675]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![63604653060005, 2175944040980, -1135184060376]] ![![-9794093090823626161085523, 1982682966035523616425244, -469750677813413640912008]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16012111, -118688, -426956]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![16012111, -118688, -426956]] 
 ![![131, 0, 0], ![0, 131, 0], ![122, 68, 1]] where
  M :=![![![16012111, -118688, -426956], ![75144256, 7781259, -237376], ![-16683040, 35317056, 7899947]]]
  hmulB := by decide  
  f := ![![![-533243932659, 107948092000, -25575793132]], ![![4501339591232, -911235910167, 215896184000]], ![![1677754186502, -339638863540, 80469540059]]]
  g := ![![![519853, 220720, -426956], ![794688, 182617, -237376], ![-7484554, -3831140, 7899947]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [80, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 130], [0, 1]]
 g := ![![[77, 113], [49, 60], [117], [112], [63], [9], [1]], ![[0, 18], [0, 71], [117], [112], [63], [9], [1]]]
 h' := ![![[128, 130], [10, 47], [4, 45], [60, 95], [51, 80], [47, 60], [51, 128], [0, 1]], ![[0, 1], [0, 84], [0, 86], [37, 36], [73, 51], [129, 71], [60, 3], [128, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [107, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [80, 3, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3000, -1612, 508]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-496, -276, 508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-533243932659, 107948092000, -25575793132]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-533243932659, 107948092000, -25575793132]] 
 ![![131, 0, 0], ![126, 1, 0], ![121, 0, 1]] where
  M :=![![![-533243932659, 107948092000, -25575793132], ![4501339591232, -911235910167, 215896184000], ![-21249533987616, 4301683543616, -1019184002167]]]
  hmulB := by decide  
  f := ![![![16012111, -118688, -426956]], ![![15974582, -54759, -412472]], ![![14662461, 159968, -334059]]]
  g := ![![![-84275057677, 107948092000, -25575793132], ![711401725254, -911235910167, 215896184000], ![-3358323635275, 4301683543616, -1019184002167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![16012111, -118688, -426956]] ![![-533243932659, 107948092000, -25575793132]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223229709, 10933284, -3285788]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![223229709, 10933284, -3285788]] 
 ![![137, 0, 0], ![0, 137, 0], ![116, 89, 1]] where
  M :=![![![223229709, 10933284, -3285788], ![578298688, 171733021, 21866568], ![-2213407328, 496881740, 160799737]]]
  hmulB := by decide  
  f := ![![![122259315732461, -24749760952244, 5863881004780]], ![![-1032043056841280, 208923293871037, -49499521904488]], ![![-531370598378780, 107568860566049, -25485943051983]]]
  g := ![![![4411541, 2214368, -3285788], ![-14293600, -12951763, 21866568], ![-152307860, -100834269, 160799737]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [49, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 136], [0, 1]]
 g := ![![[57, 14], [1], [100], [2, 135], [78], [69], [1]], ![[0, 123], [1], [100], [108, 2], [78], [69], [1]]]
 h' := ![![[84, 136], [12, 39], [46, 1], [39, 10], [44, 86], [116, 30], [88, 84], [0, 1]], ![[0, 1], [0, 98], [130, 136], [57, 127], [7, 51], [33, 107], [20, 53], [84, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [118, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [49, 53, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13569, -1736, 470]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-497, -318, 470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-122259315732461, 24749760952244, -5863881004780]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-122259315732461, 24749760952244, -5863881004780]] 
 ![![137, 0, 0], ![96, 1, 0], ![2, 0, 1]] where
  M :=![![![-122259315732461, 24749760952244, -5863881004780], ![1032043056841280, -208923293871037, 49499521904488], ![-4871979456015584, 986266986513276, -233673054823281]]]
  hmulB := by decide  
  f := ![![![-223229709, -10933284, 3285788]], ![![-160644896, -8914805, 2142840]], ![![12897430, -3786484, -1125753]]]
  g := ![![![-18149697847725, 24749760952244, -5863881004780], ![153209344705488, -208923293871037, 49499521904488], ![-723257401836814, 986266986513276, -233673054823281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![223229709, 10933284, -3285788]] ![![-122259315732461, 24749760952244, -5863881004780]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB241I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB241I2 : PrimesBelowBoundCertificateInterval O 79 137 241 where
  m := 11
  g := ![1, 2, 2, 2, 3, 2, 2, 3, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB241I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I97N1, I101N1, I103N0, I103N1, I103N2, I107N1, I109N1, I113N0, I113N1, I113N2, I127N1, I131N1, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [I109N1], [I113N0, I113N1, I113N2], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
