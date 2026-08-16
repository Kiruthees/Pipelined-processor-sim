#include <bits/stdc++.h>
using namespace std;

const int NUM_REGS = 16;
const int CACHE_SIZE = 256;

int RF[NUM_REGS] = {};
int ICache[CACHE_SIZE] = {};
int DCache[CACHE_SIZE] = {};
int reg_occupied[NUM_REGS] = {};

int PC = 0;

enum Opcode {
    ADD = 0,
    SUB = 1,
    MUL = 2,
    INC = 3,
    AND_OP = 4,
    OR_OP = 5,
    XOR_OP = 6,
    NOT_OP = 7,
    SLLI = 8,
    SRLI = 9,
    LI = 10,
    LD = 11,
    ST = 12,
    JMP = 13,
    BEQZ = 14,
    HLT = 15,
    NOP = 16
};

struct Buffer {
    bool valid = false;
    int IR = 0;
    int opcode = NOP;

    int rd = 0;
    int rs1 = 0;
    int rs2 = 0;

    int A = 0;
    int B = 0;
    int Imm = 0;

    int ALUOutput = 0;
    int LMD = 0;

    int branch_target = 0;

    int NPC = 0;   // address of the instruction right after this one,
                   // captured at fetch time (needed for PC-relative branches)
};

Buffer IF_ID;
Buffer ID_EX;
Buffer EX_MEM;
Buffer MEM_WB;

bool stop_fetch = false;

int total_inst = 0;
int arithmetic_inst = 0;
int logical_inst = 0;
int shift_inst = 0;
int memory_inst = 0;
int control_inst = 0;
int halt_inst = 0;
int li_inst = 0;

int total_cycles = 0;
int data_stalls = 0;
int control_stalls = 0;

bool pipeline_empty() {
    return !IF_ID.valid &&
           !ID_EX.valid &&
           !EX_MEM.valid &&
           !MEM_WB.valid;
}

int sign_extend(int value, int bits) {
    int mask = 1 << (bits - 1);

    if (value & mask)
        value -= (1 << bits);

    return value;
}

void load_file(const string& filename, int arr[], int size) {

    ifstream file(filename);

    if (!file) {
        cerr << "Cannot open " << filename << "\n";
        exit(1);
    }

    string value;
    int i = 0;

    while (file >> value && i < size) {

        arr[i] = stoi(value, nullptr, 16);
        i++;
    }

    file.close();
}

void load_files() {

    load_file("inst_cache.txt", ICache, CACHE_SIZE);
    load_file("data_cache.txt", DCache, CACHE_SIZE);
    load_file("reg_file.txt", RF, NUM_REGS);

    cout << "Input files loaded.\n";
}

void decode_instruction(Buffer &buf) {

    int instr = buf.IR;

    int op = (instr >> 12) & 0xF;
    int a = (instr >> 8) & 0xF;
    int b = (instr >> 4) & 0xF;
    int c = instr & 0xF;

    buf.opcode = op;

    switch (op) {

        case ADD:
        case SUB:
        case MUL:
        case AND_OP:
        case OR_OP:
        case XOR_OP:

            buf.rd = a;
            buf.rs1 = b;
            buf.rs2 = c;

            break;

        case INC:
        case NOT_OP:

            buf.rd = a;
            buf.rs1 = b;

            break;

        case SLLI:
        case SRLI:
        case LD:
        case ST:

            buf.rd = a;
            buf.rs1 = b;
            buf.Imm = c;

            break;

        case LI:

            buf.rd = a;
            buf.Imm = (b << 4) | c;

            break;

        case JMP:

            buf.Imm = (a << 4) | b;
            buf.Imm = sign_extend(buf.Imm, 8);

            break;

        case BEQZ:

            buf.rs1 = a;
            buf.Imm = (b << 4) | c;
            buf.Imm = sign_extend(buf.Imm, 8);

            break;

        case HLT:

            break;

        default:

            buf.opcode = NOP;
            break;
    }
}

bool needs_rs1(int opcode) {

    return opcode == ADD ||
           opcode == SUB ||
           opcode == MUL ||
           opcode == AND_OP ||
           opcode == OR_OP ||
           opcode == XOR_OP ||
           opcode == INC ||
           opcode == NOT_OP ||
           opcode == SLLI ||
           opcode == SRLI ||
           opcode == LD ||
           opcode == ST ||
           opcode == BEQZ;
}

bool needs_rs2(int opcode) {

    return opcode == ADD ||
           opcode == SUB ||
           opcode == MUL ||
           opcode == AND_OP ||
           opcode == OR_OP ||
           opcode == XOR_OP;
}

bool writes_register(int opcode) {

    return opcode == ADD ||
           opcode == SUB ||
           opcode == MUL ||
           opcode == INC ||
           opcode == AND_OP ||
           opcode == OR_OP ||
           opcode == XOR_OP ||
           opcode == NOT_OP ||
           opcode == SLLI ||
           opcode == SRLI ||
           opcode == LI ||
           opcode == LD;
}

bool has_data_hazard(const Buffer &buf) {

    if (!buf.valid)
        return false;

    if (needs_rs1(buf.opcode)) {

        if (reg_occupied[buf.rs1] > 0)
            return true;
    }

    if (needs_rs2(buf.opcode)) {

        if (reg_occupied[buf.rs2] > 0)
            return true;
    }

    return false;
}

void fetch_stage(Buffer &next_IF_ID) {

    next_IF_ID = Buffer();

    if (stop_fetch)
        return;

    if (PC < 0 || PC + 1 >= CACHE_SIZE) {
        stop_fetch = true;
        return;
    }

    int instruction =
        (ICache[PC] << 8) |
        ICache[PC + 1];

    next_IF_ID.valid = true;
    next_IF_ID.IR = instruction;

    PC += 2;

    next_IF_ID.NPC = PC;   // address right after this instruction
}

// Returns true if a data hazard was detected and the instruction
// currently sitting in IF_ID must be held (re-decoded) next cycle.
bool decode_stage(Buffer &next_ID_EX) {

    next_ID_EX = Buffer();

    if (!IF_ID.valid)
        return false;

    Buffer decoded = IF_ID;

    decode_instruction(decoded);

    if (decoded.opcode == NOP) {
        next_ID_EX = decoded;
        return false;
    }

    if (has_data_hazard(decoded)) {

        data_stalls++;

        next_ID_EX = Buffer();   // bubble sent down the pipeline

        return true;             // tell caller: hold IF_ID, don't fetch
    }

    next_ID_EX = decoded;

    if (writes_register(next_ID_EX.opcode)) {

        reg_occupied[next_ID_EX.rd]++;
    }

    if (next_ID_EX.opcode == HLT) {

        halt_inst++;
        total_inst++;

        stop_fetch = true;
    }

    return false;
}

void execute_stage(Buffer &next_EX_MEM,
                   bool &branch_taken,
                   int &branch_target) {

    next_EX_MEM = Buffer();

    branch_taken = false;
    branch_target = 0;

    if (!ID_EX.valid)
        return;

    next_EX_MEM = ID_EX;

    next_EX_MEM.A = RF[ID_EX.rs1];

    if (needs_rs2(ID_EX.opcode))
        next_EX_MEM.B = RF[ID_EX.rs2];

    switch (ID_EX.opcode) {

        case ADD:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A + next_EX_MEM.B;

            break;

        case SUB:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A - next_EX_MEM.B;

            break;

        case MUL:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A * next_EX_MEM.B;

            break;

        case INC:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A + 1;

            break;

        case AND_OP:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A & next_EX_MEM.B;

            break;

        case OR_OP:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A | next_EX_MEM.B;

            break;

        case XOR_OP:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A ^ next_EX_MEM.B;

            break;

        case NOT_OP:

            next_EX_MEM.ALUOutput =
                ~next_EX_MEM.A;

            break;

        case SLLI:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A << ID_EX.Imm;

            break;

        case SRLI:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A >> ID_EX.Imm;

            break;

        case LI:

            next_EX_MEM.ALUOutput =
                sign_extend(ID_EX.Imm, 8);

            break;

        case LD:
        case ST:

            next_EX_MEM.ALUOutput =
                next_EX_MEM.A +
                sign_extend(ID_EX.Imm, 4);

            break;

        case JMP:

            branch_taken = true;

            branch_target =
                ID_EX.Imm * 2;

            break;

        case BEQZ:

            if (next_EX_MEM.A == 0) {

                branch_taken = true;

                branch_target =
                    ID_EX.NPC + (ID_EX.Imm * 2);
            }

            break;

        default:

            break;
    }
}

void memory_stage(Buffer &next_MEM_WB) {

    next_MEM_WB = Buffer();

    if (!EX_MEM.valid)
        return;

    next_MEM_WB = EX_MEM;

    if (EX_MEM.opcode == LD) {

        int address =
            EX_MEM.ALUOutput;

        if (address >= 0 && address < CACHE_SIZE)
            next_MEM_WB.LMD = DCache[address];
    }

    else if (EX_MEM.opcode == ST) {

        int address =
            EX_MEM.ALUOutput;

        if (address >= 0 &&
            address < CACHE_SIZE)

            DCache[address] =
                EX_MEM.B;
    }
}

void writeback_stage() {

    if (!MEM_WB.valid)
        return;

    int op = MEM_WB.opcode;

    if (writes_register(op)) {

        if (op == LD)
            RF[MEM_WB.rd] = MEM_WB.LMD;

        else
            RF[MEM_WB.rd] = MEM_WB.ALUOutput;

        reg_occupied[MEM_WB.rd]--;

        if (reg_occupied[MEM_WB.rd] < 0)
            reg_occupied[MEM_WB.rd] = 0;
    }

    switch (op) {

        case ADD:
        case SUB:
        case MUL:
        case INC:

            arithmetic_inst++;
            total_inst++;

            break;

        case AND_OP:
        case OR_OP:
        case XOR_OP:
        case NOT_OP:

            logical_inst++;
            total_inst++;

            break;

        case SLLI:
        case SRLI:

            shift_inst++;
            total_inst++;

            break;

        case LI:

            li_inst++;
            total_inst++;

            break;

        case LD:
        case ST:

            memory_inst++;
            total_inst++;

            break;

        case JMP:
        case BEQZ:

            control_inst++;
            total_inst++;

            break;

        case HLT:

            break;

        default:

            break;
    }
}

string opcode_name(int op) {

    switch (op) {

        case ADD: return "ADD";
        case SUB: return "SUB";
        case MUL: return "MUL";
        case INC: return "INC";
        case AND_OP: return "AND";
        case OR_OP: return "OR";
        case XOR_OP: return "XOR";
        case NOT_OP: return "NOT";
        case SLLI: return "SLLI";
        case SRLI: return "SRLI";
        case LI: return "LI";
        case LD: return "LD";
        case ST: return "ST";
        case JMP: return "JMP";
        case BEQZ: return "BEQZ";
        case HLT: return "HLT";
        default: return "NOP";
    }
}

void print_pipeline(const Buffer &wb_buf) {

    cout << "\nCycle " << total_cycles << "\n";

    cout << "-----------------------------\n";

    cout << "IF  : ";

    if (IF_ID.valid)
        cout << opcode_name((IF_ID.IR >> 12) & 0xF);
    else
        cout << "NOP";

    cout << "\n";

    cout << "ID  : ";

    if (ID_EX.valid)
        cout << opcode_name(ID_EX.opcode);
    else
        cout << "NOP";

    cout << "\n";

    cout << "EX  : ";

    if (EX_MEM.valid)
        cout << opcode_name(EX_MEM.opcode);
    else
        cout << "NOP";

    cout << "\n";

    cout << "MEM : ";

    if (MEM_WB.valid)
        cout << opcode_name(MEM_WB.opcode);
    else
        cout << "NOP";

    cout << "\n";

    cout << "WB  : ";

    if (wb_buf.valid)
        cout << opcode_name(wb_buf.opcode);
    else
        cout << "NOP";

    cout << "\n";
}

void simulate() {

    while (!stop_fetch ||
           !pipeline_empty()) {

        total_cycles++;

        Buffer next_IF_ID;
        Buffer next_ID_EX;
        Buffer next_EX_MEM;
        Buffer next_MEM_WB;

        bool branch_taken = false;
        int branch_target = 0;

        Buffer wb_snapshot = MEM_WB;   // what writeback_stage() actually
                                        // consumes THIS cycle, captured
                                        // before it gets overwritten below

        writeback_stage();

        memory_stage(next_MEM_WB);

        execute_stage(
            next_EX_MEM,
            branch_taken,
            branch_target
        );

        bool decode_stalled =
            decode_stage(next_ID_EX);

        bool fetch_stalled =
            decode_stalled;

        if (branch_taken) {

            PC = branch_target;

            next_IF_ID = Buffer();
            next_ID_EX = Buffer();

            control_stalls += 2;

        }
        else if (fetch_stalled) {

            next_IF_ID = IF_ID;

        }
        else {

            fetch_stage(next_IF_ID);
        }

        MEM_WB = next_MEM_WB;
        EX_MEM = next_EX_MEM;
        ID_EX = next_ID_EX;
        IF_ID = next_IF_ID;

        RF[0] = 0;

        print_pipeline(wb_snapshot);
    }
}

void write_output() {

    ofstream out("Output.txt");

    out << "Total number of instructions executed:"
        << total_inst << '\n';

    out << "Number of instructions in each class\n";

    out << "Arithmetic instructions              :"
        << arithmetic_inst << '\n';

    out << "Logical instructions                 :"
        << logical_inst << '\n';

    out << "Shift instructions                   :"
        << shift_inst << '\n';

    out << "Memory instructions                  :"
        << memory_inst << '\n';

    out << "Load immediate instructions          :"
        << li_inst << '\n';

    out << "Control instructions                 :"
        << control_inst << '\n';

    out << "Halt instructions                    :"
        << halt_inst << '\n';

    if (total_inst != 0) {

        out << "Cycles Per Instruction               :"
            << (double)total_cycles / total_inst
            << '\n';
    }

    out << "Total number of stalls               :"
        << data_stalls + control_stalls << '\n';

    out << "Data stalls (RAW)                    :"
        << data_stalls << '\n';

    out << "Control stalls                       :"
        << control_stalls << '\n';

    out.close();

    ofstream dcache_out("ODCache.txt");

    for (int i = 0; i < CACHE_SIZE; i++) {

        dcache_out
            << hex
            << setw(2)
            << setfill('0')
            << DCache[i]
            << '\n';
    }

    dcache_out.close();
}

void print_final_state() {

    cout << "\n========== REGISTERS ==========\n";

    for (int i = 0; i < NUM_REGS; i++) {

        cout << "R"
             << i
             << " = "
             << RF[i]
             << '\n';
    }

    cout << "\n========== STATISTICS ==========\n";

    cout << "Instructions : "
         << total_inst << '\n';

    cout << "Cycles       : "
         << total_cycles << '\n';

    cout << "Data stalls  : "
         << data_stalls << '\n';

    cout << "Control stalls : "
         << control_stalls << '\n';

    cout << "Total stalls : "
         << data_stalls + control_stalls << '\n';
}

int main() {

    load_files();

    simulate();

    write_output();

    print_final_state();

    return 0;
}