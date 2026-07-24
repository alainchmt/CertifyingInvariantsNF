
import IdealArithmetic.Examples.NF3_1_482727_1.RI3_1_482727_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163685616999719, 6292905217220, -8174338289739]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-163685616999719, 6292905217220, -8174338289739]] 
 ![![83, 0, 0], ![1, 1, 0], ![55, 0, 1]] where
  M :=![![![-163685616999719, 6292905217220, -8174338289739], ![806729451611979, -31014771291376, 40287470375502], ![-406701954826528, 15635685653345, -20310393929455]]]
  hmulB := by decide  
  f := ![![![-41525890, -6688145, 3446424]], ![![-4452413, -1206206, -600651]], ![![-20541219, -3684890, 957932]]]
  g := ![![![3368796189382, 6292905217220, -8174338289739], ![-16603212623485, -31014771291376, 40287470375502], ![8370289465544, 15635685653345, -20310393929455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 4]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-5, 1, 4]] 
 ![![83, 0, 0], ![28, 1, 0], ![54, 0, 1]] where
  M :=![![![-5, 1, 4], ![-407, -74, 17], ![-213, -77, -67]]]
  hmulB := by decide  
  f := ![![![6267, -241, 313]], ![![1742, -67, 87]], ![![4265, -164, 213]]]
  g := ![![![-3, 1, 4], ![9, -74, 17], ![67, -77, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![469796, 95781, 911]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![469796, 95781, 911]] 
 ![![83, 0, 0], ![53, 1, 0], ![7, 0, 1]] where
  M :=![![![469796, 95781, 911], ![-379354, 358528, 863851], ![-9699389, -1641942, 646782]]]
  hmulB := by decide  
  f := ![![![-1650282695538, 63445235904, -82413893623]], ![![-955801389341, 36745852567, -47732012363]], ![![-188582634622, 7250072835, -9417676881]]]
  g := ![![![-55578, 95781, 911], ![-306365, 358528, 863851], ![877061, -1641942, 646782]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-163685616999719, 6292905217220, -8174338289739]] ![![-5, 1, 4]]
  ![![-1650282695538, 63445235904, -82413893623]] where
 M := ![![![-1650282695538, 63445235904, -82413893623]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-1650282695538, 63445235904, -82413893623]] ![![469796, 95781, 911]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9952375928645468, 382619802234764, -497014271128923]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-9952375928645468, 382619802234764, -497014271128923]] 
 ![![89, 0, 0], ![22, 1, 0], ![67, 0, 1]] where
  M :=![![![-9952375928645468, 382619802234764, -497014271128923], ![49050581977316931, -1885753121688541, 2449549677855030], ![-24728200434101320, 950677428942857, -1234907986113172]]]
  hmulB := by decide  
  f := ![![![38458658, 30241603, 44508423]], ![![-42022304, -933830, 15060411]], ![![-19369749, 9488245, 26616533]]]
  g := ![![![167752186380085, 382619802234764, -497014271128923], ![-826771660245193, -1885753121688541, 2449549677855030], ![416805968525150, 950677428942857, -1234907986113172]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4895865, -524571, 929909]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-4895865, -524571, 929909]] 
 ![![89, 0, 0], ![75, 1, 0], ![6, 0, 1]] where
  M :=![![![-4895865, -524571, 929909], ![-92347096, -20179747, -2861321], ![26944219, -5030928, -20823551]]]
  hmulB := by decide  
  f := ![![![405818890885709, -15601736197173, 20266294371314]], ![![319509284196820, -12283557213679, 15956056638389]], ![![38688005155415, -1487363116863, 1932050278407]]]
  g := ![![![324354, -524571, 929909], ![16160695, -20179747, -2861321], ![5946125, -5030928, -20823551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, -2]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![0, -1, -2]] 
 ![![89, 0, 0], ![80, 1, 0], ![49, 0, 1]] where
  M :=![![![0, -1, -2], ![205, 35, -13], ![157, 47, 30]]]
  hmulB := by decide  
  f := ![![![-1661, 64, -83]], ![![-1401, 54, -70]], ![![-961, 37, -48]]]
  g := ![![![2, -1, -2], ![-22, 35, -13], ![-57, 47, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-9952375928645468, 382619802234764, -497014271128923]] ![![-4895865, -524571, 929909]]
  ![![-1661, 64, -83]] where
 M := ![![![-1661, 64, -83]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-1661, 64, -83]] ![![0, -1, -2]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1081549145, 41580234, -54011762]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-1081549145, 41580234, -54011762]] 
 ![![97, 0, 0], ![0, 97, 0], ![63, 27, 1]] where
  M :=![![![-1081549145, 41580234, -54011762], ![5330447260, -204929425, 266198582], ![-2687274298, 103312452, -134200485]]]
  hmulB := by decide  
  f := ![![![-4413, -1578, -1354]], ![![141488, 20183, -16910]], ![![38551, 5079, -5441]]]
  g := ![![![23929813, 15462864, -54011762], ![-117938798, -76209187, 266198582], ![59457281, 38419851, -134200485]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [4, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 96], [0, 1]]
 g := ![![[45, 73], [62], [62], [24], [4], [14, 1]], ![[0, 24], [62], [62], [24], [4], [28, 96]]]
 h' := ![![[14, 96], [7, 48], [35, 16], [63, 81], [16, 86], [41, 95], [0, 1]], ![[0, 1], [0, 49], [65, 81], [33, 16], [56, 11], [13, 2], [14, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [96, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [4, 83, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1259, -1662, -3435]
  a := ![4, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2218, 939, -3435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4413, 1578, 1354]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![4413, 1578, 1354]] 
 ![![97, 0, 0], ![46, 1, 0], ![93, 0, 1]] where
  M :=![![![4413, 1578, 1354], ![-141488, -20183, 16910], ![-197290, -47136, -14095]]]
  hmulB := by decide  
  f := ![![![1081549145, -41580234, 54011762]], ![![457946530, -17605787, 22869510]], ![![1064653039, -40930662, 53167983]]]
  g := ![![![-2001, 1578, 1354], ![-8100, -20183, 16910], ![33833, -47136, -14095]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-1081549145, 41580234, -54011762]] ![![4413, 1578, 1354]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143852424534952544873, 5530416718698645642, -7183883370460528730]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-143852424534952544873, 5530416718698645642, -7183883370460528730]] 
 ![![101, 0, 0], ![0, 101, 0], ![85, 80, 1]] where
  M :=![![![-143852424534952544873, 5530416718698645642, -7183883370460528730], ![708980970260417464804, -27256823955822202105, 35405983727366753318], ![-357423354215668405402, 13741166339030955036, -17849457170186793909]]]
  hmulB := by decide  
  f := ![![![-4495239297, -782760498, 256527094]], ![![-23560955000, -8073439397, -6531790294]], ![![-21733620679, -6959908634, -5058451627]]]
  g := ![![![4621561009447449477, 5744961251044959842, -7183883370460528730], ![-22777501451146104626, -28314213090546163045, 35405983727366753318], ![11482975299507020563, 14274235049049252156, -17849457170186793909]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [4, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 100], [0, 1]]
 g := ![![[91, 76], [70], [30, 71], [80], [97], [40, 1]], ![[0, 25], [70], [42, 30], [80], [97], [80, 100]]]
 h' := ![![[40, 100], [81, 51], [82, 75], [13, 24], [63, 79], [42, 81], [0, 1]], ![[0, 1], [0, 50], [52, 26], [64, 77], [92, 22], [50, 20], [40, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [24, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [4, 61, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![519, -4110, -5619]
  a := ![-7, -3, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4734, 4410, -5619]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4495239297, 782760498, -256527094]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![4495239297, 782760498, -256527094]] 
 ![![101, 0, 0], ![86, 1, 0], ![74, 0, 1]] where
  M :=![![![4495239297, 782760498, -256527094], ![23560955000, 8073439397, 6531790294], ![-71876051666, -9459022056, 10165193797]]]
  hmulB := by decide  
  f := ![![![143852424534952544873, -5530416718698645642, 7183883370460528730]], ![![115468589502430706874, -4439198156953082407, 5766415704279591262]], ![![108935670988140165604, -4188039638838918144, 5440166599844217029]]]
  g := ![![![-434051075, 782760498, -256527094], ![-11426805098, 8073439397, 6531790294], ![-105193028, -9459022056, 10165193797]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-143852424534952544873, 5530416718698645642, -7183883370460528730]] ![![4495239297, 782760498, -256527094]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [74, 50, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 99, 22], [7, 3, 81], [0, 1]]
 g := ![![[69, 102, 2], [33, 3, 76], [43, 75, 64], [101, 97], [37, 26], [1]], ![[101, 96, 89, 87], [32, 93, 76, 39], [57, 101, 35, 39], [80, 56], [75, 91], [90, 65, 95, 39]], ![[45, 100, 38, 17], [91, 2, 9, 34], [19, 47, 91, 14], [72, 7], [36, 34], [94, 88, 101, 64]]]
 h' := ![![[44, 99, 22], [30, 0, 38], [11, 80, 73], [40, 77, 95], [60, 21, 71], [29, 53, 51], [0, 1]], ![[7, 3, 81], [36, 15, 11], [8, 91, 22], [44, 90, 22], [14, 66, 57], [38, 6, 83], [44, 99, 22]], ![[0, 1], [96, 88, 54], [31, 35, 8], [23, 39, 89], [43, 16, 78], [82, 44, 72], [7, 3, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 43], []]
 b := ![[], [28, 5, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [74, 50, 52, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-655998760, -170077823, -74919419]
  a := ![2, 1, -70]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6368920, -1651241, -727373]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-148759979, 5719088, -7428963]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-148759979, 5719088, -7428963]] 
 ![![107, 0, 0], ![18, 1, 0], ![37, 0, 1]] where
  M :=![![![-148759979, 5719088, -7428963], ![733167999, -28186696, 36613866], ![-369616924, 14209949, -18458395]]]
  hmulB := by decide  
  f := ![![![39914, 9127, 2040]], ![![4533, 1499, 1149]], ![![4653, 1420, 944]]]
  g := ![![![216524, 5719088, -7428963], ![-1067145, -28186696, 36613866], ![537987, 14209949, -18458395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35175852, 10331283, 6335768]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![35175852, 10331283, 6335768]] 
 ![![107, 0, 0], ![37, 1, 0], ![30, 0, 1]] where
  M :=![![![35175852, 10331283, 6335768], ![-670906417, -82863487, 105653083], ![-1220861087, -270668331, -45533870]]]
  hmulB := by decide  
  f := ![![![32370038885419163, -1244468453107998, 1616535729598505]], ![![9702380704956860, -373008718034050, 484529695106259]], ![![9827378316801164, -377814260134407, 490771983117591]]]
  g := ![![![-5020137, 10331283, 6335768], ![-7238784, -82863487, 105653083], ![94952180, -270668331, -45533870]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-165656085, 6368660, -8272742]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-165656085, 6368660, -8272742]] 
 ![![107, 0, 0], ![51, 1, 0], ![73, 0, 1]] where
  M :=![![![-165656085, 6368660, -8272742], ![816440962, -31388131, 40772456], ![-411597884, 15823910, -20554893]]]
  hmulB := by decide  
  f := ![![![47977, 7840, -3758]], ![![26195, 4709, -1202]], ![![26315, 4630, -1407]]]
  g := ![![![1060303, 6368660, -8272742], ![-5225735, -31388131, 40772456], ![2634485, 15823910, -20554893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-148759979, 5719088, -7428963]] ![![35175852, 10331283, 6335768]]
  ![![47977, 7840, -3758]] where
 M := ![![![47977, 7840, -3758]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![47977, 7840, -3758]] ![![-165656085, 6368660, -8272742]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [80, 47, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 15, 62], [37, 93, 47], [0, 1]]
 g := ![![[101, 83, 89], [4, 36], [84, 11, 1], [95, 87, 3], [86, 93], [1]], ![[52, 89, 69, 54], [63, 105], [63, 104, 60, 58], [104, 6, 102, 65], [103, 35], [76, 101, 40, 54]], ![[103, 9, 90, 41], [47, 3], [86, 60, 36, 32], [48, 42, 100, 56], [49, 12], [25, 19, 91, 55]]]
 h' := ![![[95, 15, 62], [34, 7, 31], [38, 105, 103], [30, 103, 1], [65, 71, 60], [29, 62, 23], [0, 1]], ![[37, 93, 47], [12, 39, 47], [16, 2, 66], [18, 45, 48], [69, 9, 63], [5, 2, 97], [95, 15, 62]], ![[0, 1], [77, 63, 31], [83, 2, 49], [12, 70, 60], [108, 29, 95], [39, 45, 98], [37, 93, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 105], []]
 b := ![[], [38, 96, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [80, 47, 86, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15999129, -5331408, -4101016]
  a := ![8, 3, -23]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-146781, -48912, -37624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [98, 106, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 79, 8], [78, 33, 105], [0, 1]]
 g := ![![[7, 13, 72], [9, 25], [23, 95], [29, 57], [58, 8, 41], [1]], ![[58, 2, 17, 9], [74, 109], [75, 95], [70, 56], [97, 49, 31, 53], [2, 59, 45, 60]], ![[29, 17, 34, 62], [92, 60], [], [36, 98], [87, 84, 106, 1], [63, 80, 102, 53]]]
 h' := ![![[105, 79, 8], [20, 18, 33], [87, 95, 108], [9, 49, 35], [79, 73, 82], [15, 7, 70], [0, 1]], ![[78, 33, 105], [41, 109, 103], [93, 85, 30], [18, 102, 78], [18, 104, 13], [83, 21, 106], [105, 79, 8]], ![[0, 1], [23, 99, 90], [15, 46, 88], [44, 75], [42, 49, 18], [106, 85, 50], [78, 33, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 63], []]
 b := ![[], [20, 26, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [98, 106, 43, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2757313, -835296, -543756]
  a := ![4, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24401, -7392, -4812]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀


def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3132105, 120414, -156415]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-3132105, 120414, -156415]] 
 ![![127, 0, 0], ![59, 1, 0], ![71, 0, 1]] where
  M :=![![![-3132105, 120414, -156415], ![15436673, -593464, 770896], ![-7782194, 299187, -388637]]]
  hmulB := by decide  
  f := ![![![-7016, -1113, 616]], ![![-3723, -646, 217]], ![![-3173, -546, 194]]]
  g := ![![![6842, 120414, -156415], ![-33721, -593464, 770896], ![17000, 299187, -388637]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42, 6, -5]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![42, 6, -5]] 
 ![![127, 0, 0], ![97, 1, 0], ![108, 0, 1]] where
  M :=![![![42, 6, -5], ![487, 121, 44], ![-466, -27, 134]]]
  hmulB := by decide  
  f := ![![![17402, -669, 869]], ![![12616, -485, 630]], ![![15139, -582, 756]]]
  g := ![![![0, 6, -5], ![-126, 121, 44], ![-97, -27, 134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-3132105, 120414, -156415]] ![![42, 6, -5]]
  ![![-17402, 669, -869]] where
 M := ![![![-17402, 669, -869]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-17402, 669, -869]] ![![42, 6, -5]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20546821, -789924, 1026093]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![20546821, -789924, 1026093]] 
 ![![131, 0, 0], ![0, 131, 0], ![22, 26, 1]] where
  M :=![![![20546821, -789924, 1026093], ![-101265621, 3893164, -5057130], ![51051720, -1962687, 2549485]]]
  hmulB := by decide  
  f := ![![![-670, -21, 228]], ![![-22965, -4525, 267]], ![![-4703, -925, 58]]]
  g := ![![![-15475, -209682, 1026093], ![76269, 1033424, -5057130], ![-38450, -520987, 2549485]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [64, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 130], [0, 1]]
 g := ![![[80, 43], [10, 38], [94], [60], [34], [121], [1]], ![[0, 88], [116, 93], [94], [60], [34], [121], [1]]]
 h' := ![![[120, 130], [15, 49], [87, 13], [48, 15], [58, 86], [20, 77], [67, 120], [0, 1]], ![[0, 1], [0, 82], [75, 118], [14, 116], [29, 45], [90, 54], [57, 11], [120, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [101, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [64, 11, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-111855, -65025, -74294]
  a := ![-22, -1, 67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11623, 14249, -74294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![670, 21, -228]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![670, 21, -228]] 
 ![![131, 0, 0], ![26, 1, 0], ![73, 0, 1]] where
  M :=![![![670, 21, -228], ![22965, 4525, -267], ![4263, 3063, 4360]]]
  hmulB := by decide  
  f := ![![![-20546821, 789924, -1026093]], ![![-3304975, 127060, -165048]], ![![-11839463, 455169, -591254]]]
  g := ![![![128, 21, -228], ![-574, 4525, -267], ![-3005, 3063, 4360]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![20546821, -789924, 1026093]] ![![670, 21, -228]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [96, 131, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 71, 53], [90, 65, 84], [0, 1]]
 g := ![![[12, 100, 60], [24, 4], [23, 130], [90, 76, 130], [15, 109], [34, 1], []], ![[8, 36, 112, 83], [52, 119], [3, 50], [131, 65, 35, 80], [4, 32], [116, 115], [8, 69]], ![[128, 107, 37, 102], [69, 50], [64, 88], [103, 49, 116, 3], [14, 76], [37, 109], [114, 69]]]
 h' := ![![[81, 71, 53], [3, 93, 103], [65, 109, 2], [128, 77, 104], [95, 16, 104], [24, 108, 66], [0, 0, 1], [0, 1]], ![[90, 65, 84], [45, 94, 116], [67, 55, 16], [9, 48, 18], [104, 101, 73], [112, 11, 13], [39, 131, 65], [81, 71, 53]], ![[0, 1], [127, 87, 55], [77, 110, 119], [78, 12, 15], [35, 20, 97], [3, 18, 58], [33, 6, 71], [90, 65, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 136], []]
 b := ![[], [117, 86, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [96, 131, 103, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20276, 2466, -1507]
  a := ![0, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![148, 18, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB197I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB197I2 : PrimesBelowBoundCertificateInterval O 79 137 197 where
  m := 11
  g := ![3, 3, 2, 2, 1, 3, 1, 1, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB197I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![83, 83, 83]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N0, I83N1, I83N2, I89N0, I89N1, I89N2, I97N1, I101N1, I107N0, I107N1, I107N2, I127N0, I127N1, I131N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N0, I89N1, I89N2], [I97N1], [I101N1], [], [I107N0, I107N1, I107N2], [], [], [I127N0, I127N1, I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
