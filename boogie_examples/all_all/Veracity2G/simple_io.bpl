// https://github.com/veracity-lang/veracity2g/blob/main/benchmarks/global_commutativity/simple-io.vcy

// commutativity{
//     {f1(fname_1, fname_2)}, {f2(fname_3, fname_4)} : ((fname_2 != fname_3) && (fname_1 != fname_4) && (fname_2 != fname_4))
// }

// int main(int argc, string[] argv) {
//     string fname = "a.txt";
// 	in_channel i = open_read(fname);
//     out_channel o = open_write(fname);
// 	string fname_1 = argv[1];
// 	string fname_2 = argv[2];
// 	string fname_3 = argv[3];
// 	string fname_4 = argv[4];
// 	string temp = "";
//     int j = 0;
//     int k = 0;
//     int z = 0;

// 	f1(fname_1, fname_2): {
//         while(k < 20) {
//             k = k + 1;
//             cp(fname_1, fname_2);
//         }
// 	}

// 	f2(fname_3, fname_4): {
//         /* amplify problem size 10x */
//         while(z < 10) {
//             z = z + 1;

//             i = open_read(fname_3);
//             o = open_write(fname_4);
//             temp = read_line(i);
//             write(o, temp);
//             close(i);
//             close(o);
//         }

//     }

// 	return 0;
// }


// File system model (from vcylib.ml)
// --------------------------------------------
// file_system[filename][line_number] = content
var file_system, file_system': [int][int]int;
// open_files[filename] = true if file is currently open
var open_files, open_files': [int]bool;
// file_pointers[filename] = current line number
var file_pointers, file_pointers': [int]int;


// f1
procedure f1(fname_1: int, fname_2: int)
  modifies file_system;
  ensures file_system[fname_2] == old(file_system[fname_1]);
  ensures (forall f: int :: f != fname_2 ==> file_system[f] == old(file_system[f]));
{
    var k: int;
    k := 0;
    while (k < 20)
      invariant 0 <= k && k <= 20;
      invariant (forall f: int :: f != fname_2 ==> file_system[f] == old(file_system[f]));
      invariant file_system[fname_1] == old(file_system[fname_1]);
      invariant k > 0 ==> file_system[fname_2] == old(file_system[fname_1]);
    {
        k := k + 1;
        // cp copies the entire file content: file_system[to] := file_system[from]
        file_system := file_system[fname_2 := file_system[fname_1]];
    }
}

// Primed version for biprogram execution (right side)
procedure f1_primed(fname_1: int, fname_2: int)
  modifies file_system';
  ensures file_system'[fname_2] == old(file_system'[fname_1]);
  ensures (forall f: int :: f != fname_2 ==> file_system'[f] == old(file_system'[f]));
{
    var k: int;
    k := 0;
    while (k < 20)
      invariant 0 <= k && k <= 20;
      invariant (forall f: int :: f != fname_2 ==> file_system'[f] == old(file_system'[f]));
      invariant file_system'[fname_1] == old(file_system'[fname_1]);
      invariant k > 0 ==> file_system'[fname_2] == old(file_system'[fname_1]);
    {
        k := k + 1;
        file_system' := file_system'[fname_2 := file_system'[fname_1]];
    }
}


// f2: open, read, write, close on fname_3 and fname_4, repeated 10 times ---
// open_read/open_write: sets linenum to 0, adds to opened set
// read_line: reads data at [fname][linenum], increments linenum 
// write: writes data[fname][linenum] := content, increments linenum
// close: removes from opened set
// open_read and open_write share the realWorld_linenum pointer keyed by filename. 
procedure f2(fname_3: int, fname_4: int)
  requires fname_3 != fname_4;
  requires !open_files[fname_3] && !open_files[fname_4];
  ensures file_system[fname_4][0] == old(file_system[fname_3][0]);
  ensures (forall line: int :: line != 0 ==> file_system[fname_4][line] == old(file_system[fname_4][line]));
  ensures (forall f: int :: f != fname_4 ==> file_system[f] == old(file_system[f]));
  ensures (forall f: int :: open_files[f] == old(open_files[f]));
  modifies file_system, open_files, file_pointers;
{
    var z: int;
    var temp: int;

    z := 0;
    while (z < 10)
      invariant 0 <= z && z <= 10;
      invariant !open_files[fname_3] && !open_files[fname_4];
      invariant (forall f: int :: f != fname_3 && f != fname_4 ==> open_files[f] == old(open_files[f]));
      invariant (forall f: int :: f != fname_4 ==> file_system[f] == old(file_system[f]));
      invariant (file_system[fname_3][0] == old(file_system[fname_3][0]));
      invariant z > 0 ==> file_system[fname_4][0] == old(file_system[fname_3][0]);
      invariant (forall line: int :: line != 0 ==> file_system[fname_4][line] == old(file_system[fname_4][line]));
    {
        z := z + 1;

        // i = open_read(fname_3): sets linenum to 0, adds to opened
        open_files[fname_3] := true;
        file_pointers[fname_3] := 0;

        // o = open_write(fname_4): sets linenum to 0, adds to opened
        open_files[fname_4] := true;
        file_pointers[fname_4] := 0;

        // temp = read_line(i): reads data[fname_3][linenum], increments linenum
        assert open_files[fname_3];
        temp := file_system[fname_3][file_pointers[fname_3]];
        file_pointers[fname_3] := file_pointers[fname_3] + 1;

        // write(o, temp): writes data[fname_4][linenum] := temp, increments linenum
        assert open_files[fname_4];
        file_system := file_system[fname_4 := file_system[fname_4][file_pointers[fname_4] := temp]];
        file_pointers[fname_4] := file_pointers[fname_4] + 1;

        // close(i): removes from opened
        open_files[fname_3] := false;

        // close(o): removes from opened
        open_files[fname_4] := false;
    }
}

// Primed version for biprogram execution (right side)
procedure f2_primed(fname_3: int, fname_4: int)
  requires fname_3 != fname_4;
  requires !open_files'[fname_3] && !open_files'[fname_4];
  ensures file_system'[fname_4][0] == old(file_system'[fname_3][0]);
  ensures (forall line: int :: line != 0 ==> file_system'[fname_4][line] == old(file_system'[fname_4][line]));
  ensures (forall f: int :: f != fname_4 ==> file_system'[f] == old(file_system'[f]));
  ensures (forall f: int :: open_files'[f] == old(open_files'[f]));
  modifies file_system', open_files', file_pointers';
{
    var z: int;
    var temp: int;

    z := 0;
    while (z < 10)
      invariant 0 <= z && z <= 10;
      invariant !open_files'[fname_3] && !open_files'[fname_4];
      invariant (forall f: int :: f != fname_3 && f != fname_4 ==> open_files'[f] == old(open_files'[f]));
      invariant (forall f: int :: f != fname_4 ==> file_system'[f] == old(file_system'[f]));
      invariant file_system'[fname_3][0] == old(file_system'[fname_3][0]);
      invariant z > 0 ==> file_system'[fname_4][0] == old(file_system'[fname_3][0]);
      invariant (forall line: int :: line != 0 ==> file_system'[fname_4][line] == old(file_system'[fname_4][line]));
    {
        z := z + 1;

        open_files'[fname_3] := true;
        file_pointers'[fname_3] := 0;

        open_files'[fname_4] := true;
        file_pointers'[fname_4] := 0;

        assert open_files'[fname_3];
        temp := file_system'[fname_3][file_pointers'[fname_3]];
        file_pointers'[fname_3] := file_pointers'[fname_3] + 1;

        assert open_files'[fname_4];
        file_system' := file_system'[fname_4 := file_system'[fname_4][file_pointers'[fname_4] := temp]];
        file_pointers'[fname_4] := file_pointers'[fname_4] + 1;

        open_files'[fname_3] := false;

        open_files'[fname_4] := false;
    }
}


// --- Commutativity check ---
// f1(fname_1, fname_2) commutes with f2(fname_3, fname_4)
// when (fname_2 != fname_3) && (fname_1 != fname_4) && (fname_2 != fname_4)
// The condition ensures:
//   fname_2 != fname_3: f1's writes don't affect f2's reads
//   fname_1 != fname_4: f2's writes don't affect f1's reads
//   fname_2 != fname_4: f1 and f2 write to different files

procedure commutativity_check(fname_1: int, fname_2: int, fname_3: int, fname_4: int)
  // Well-formedness: can't open_read and open_write the same file
  requires fname_3 != fname_4;
  // Commutativity condition from Veracity spec
  requires fname_2 != fname_3;
  requires fname_1 != fname_4;
  requires fname_2 != fname_4;
  modifies file_system, file_system', open_files, open_files', file_pointers, file_pointers';
{
    var z, z': int;
    var temp, temp': int;
    var k, k': int;

    // Assume identical initial file system states
    assume (forall f: int, line: int :: file_system[f][line] == file_system'[f][line]);

    assume (forall f: int :: open_files[f] == open_files'[f]);
    assume (!open_files[fname_1] && !open_files[fname_2] && !open_files[fname_3] && !open_files[fname_4]);

    assume (forall f: int :: file_pointers[f] == file_pointers'[f]);


    // Left execution
    // f1; f2

    k := 0;
    while (k < 20)
      invariant (forall f: int :: f != fname_2 ==> file_system[f] == old(file_system[f]));
      invariant file_system[fname_1] == old(file_system[fname_1]);
      invariant k > 0 ==> file_system[fname_2] == old(file_system[fname_1]);
    {
        k := k + 1;
        file_system := file_system[fname_2 := file_system[fname_1]];
    }

    z := 0;
    while (z < 10)
      invariant !open_files[fname_3] && !open_files[fname_4];
      invariant (forall f: int :: f != fname_3 && f != fname_4 ==> open_files[f] == old(open_files[f]));
      invariant (forall f: int :: f != fname_4 && f != fname_2 ==> file_system[f] == old(file_system[f]));
      invariant file_system[fname_2] == old(file_system[fname_1]);
      invariant z > 0 ==> file_system[fname_4][0] == old(file_system[fname_3][0]);
      invariant (forall line: int :: line != 0 ==> file_system[fname_4][line] == old(file_system[fname_4][line]));
    {
        z := z + 1;

        open_files[fname_3] := true;
        file_pointers[fname_3] := 0;

        open_files[fname_4] := true;
        file_pointers[fname_4] := 0;

        assert open_files[fname_3];
        temp := file_system[fname_3][file_pointers[fname_3]];
        file_pointers[fname_3] := file_pointers[fname_3] + 1;

        assert open_files[fname_4];
        file_system := file_system[fname_4 := file_system[fname_4][file_pointers[fname_4] := temp]];
        file_pointers[fname_4] := file_pointers[fname_4] + 1;

        open_files[fname_3] := false;

        open_files[fname_4] := false;
    }

    // Right execution
    // f2 ; f1

    z' := 0;
    while (z' < 10)
      invariant !open_files'[fname_3] && !open_files'[fname_4];
      invariant (forall f: int :: f != fname_3 && f != fname_4 ==> open_files'[f] == old(open_files'[f]));
      invariant (forall f: int :: f != fname_4 ==> file_system'[f] == old(file_system'[f]));
      invariant z' > 0 ==> file_system'[fname_4][0] == old(file_system'[fname_3][0]);
      invariant (forall line: int :: line != 0 ==> file_system'[fname_4][line] == old(file_system'[fname_4][line]));
    {
        z' := z' + 1;

        open_files'[fname_3] := true;
        file_pointers'[fname_3] := 0;

        open_files'[fname_4] := true;
        file_pointers'[fname_4] := 0;

        assert open_files'[fname_3];
        temp' := file_system'[fname_3][file_pointers'[fname_3]];
        file_pointers'[fname_3] := file_pointers'[fname_3] + 1;

        assert open_files'[fname_4];
        file_system' := file_system'[fname_4 := file_system'[fname_4][file_pointers'[fname_4] := temp']];
        file_pointers'[fname_4] := file_pointers'[fname_4] + 1;

        open_files'[fname_3] := false;

        open_files'[fname_4] := false;
    }

    k' := 0;
    while (k' < 20)
      invariant (forall f: int :: f != fname_2 && f != fname_4 ==> file_system'[f] == old(file_system'[f]));
      invariant file_system'[fname_4][0] == old(file_system'[fname_3][0]);
      invariant (forall line: int :: line != 0 ==> file_system'[fname_4][line] == old(file_system'[fname_4][line]));
      invariant file_system'[fname_1] == old(file_system'[fname_1]);
      invariant k' > 0 ==> file_system'[fname_2] == old(file_system'[fname_1]);
    {
        k' := k' + 1;
        file_system' := file_system'[fname_2 := file_system'[fname_1]];
    }

    // Assert both executions produce the same final file system state
    assert (forall f: int, line: int :: file_system[f][line] == file_system'[f][line]);
    assert (forall f: int :: open_files[f] == open_files'[f]);
    assume (forall f: int :: file_pointers[f] == file_pointers'[f]);
}
