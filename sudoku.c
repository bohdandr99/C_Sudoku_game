// sudoku.c - single-file, single-thread terminal Sudoku game
// Build: gcc -std=c2x -O2 -Wall -Wextra -o sudoku sudoku.c
// (Use -std=c23 if your GCC prefers the finalized name.)

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>

#define N 9
#define BOX 3
#define ALL ((1<<9)-1)

typedef struct {
    int grid[N][N];       // 0 == empty, 1..9 == value
} Board;

typedef struct {
    unsigned row[N], col[N], box[N];
} Masks;

static inline int box_index(int r, int c){ return (r/BOX)*BOX + (c/BOX); }
static inline int popcount9(unsigned x){ return __builtin_popcount(x); }
static inline int lsb_index(unsigned x){ return __builtin_ctz(x); }

static void masks_init(Masks* m, const Board* b){
    for(int i=0;i<N;i++){ m->row[i]=m->col[i]=m->box[i]=0; }
    for(int i=0;i<N;i++){
        for(int j=0;j<N;j++){
            int v=b->grid[i][j];
            if(v){
                unsigned bit=1u<<(v-1);
                m->row[i]|=bit; m->col[j]|=bit; m->box[box_index(i,j)]|=bit;
            }
        }
    }
}

static inline unsigned used_mask(const Masks* m, int r, int c){
    return m->row[r] | m->col[c] | m->box[box_index(r,c)];
}

static inline unsigned candidates_mask(const Masks* m, int r, int c){
    return (~used_mask(m,r,c)) & ALL;
}

static void apply_set(Board* b, Masks* m, int r, int c, int v){
    b->grid[r][c]=v;
    unsigned bit = 1u<<(v-1);
    m->row[r] |= bit; m->col[c] |= bit; m->box[box_index(r,c)] |= bit;
}

static void apply_clear(Board* b, Masks* m, int r, int c){
    int v=b->grid[r][c];
    if(!v) return;
    unsigned bit=1u<<(v-1);
    m->row[r] &= ~bit; m->col[c] &= ~bit; m->box[box_index(r,c)] &= ~bit;
    b->grid[r][c]=0;
}

static void copy_board(Board* dst, const Board* src){
    memcpy(dst, src, sizeof(Board));
}

static void print_board(const Board* b){
    printf("    1 2 3   4 5 6   7 8 9\n");
    printf("  +-------+-------+-------+\n");
    for(int r=0;r<N;r++){
        printf("%d |", r+1);
        for(int c=0;c<N;c++){
            int v=b->grid[r][c];
            if(v) printf(" %d", v);
            else  printf(" .");
            if((c+1)%3==0) printf(" |");
        }
        printf("\n");
        if((r+1)%3==0) printf("  +-------+-------+-------+\n");
    }
}

static bool is_legal(const Board* b){
    // rows
    for(int r=0;r<N;r++){
        int used=0;
        for(int c=0;c<N;c++){
            int v=b->grid[r][c];
            if(!v) continue;
            int bit=1<<(v-1);
            if(used & bit) return false;
            used |= bit;
        }
    }
    // cols
    for(int c=0;c<N;c++){
        int used=0;
        for(int r=0;r<N;r++){
            int v=b->grid[r][c];
            if(!v) continue;
            int bit=1<<(v-1);
            if(used & bit) return false;
            used |= bit;
        }
    }
    // boxes
    for(int br=0;br<N;br+=3){
        for(int bc=0;bc<N;bc+=3){
            int used=0;
            for(int dr=0;dr<3;dr++) for(int dc=0;dc<3;dc++){
                int v=b->grid[br+dr][bc+dc];
                if(!v) continue;
                int bit=1<<(v-1);
                if(used & bit) return false;
                used |= bit;
            }
        }
    }
    return true;
}

typedef struct { int r,c; unsigned cand; } Choice;

static bool find_best_cell(const Board* b, const Masks* m, Choice* ch){
    unsigned bestMask=0; int bestR=-1, bestC=-1; int bestCount=10;
    for(int r=0;r<N;r++){
        for(int c=0;c<N;c++){
            if(b->grid[r][c]) continue;
            unsigned cand=candidates_mask(m,r,c);
            int cnt=popcount9(cand);
            if(cnt==0) return false; // dead
            if(cnt<bestCount){
                bestCount=cnt; bestMask=cand; bestR=r; bestC=c;
                if(cnt==1) goto done; // MRV shortcut
            }
        }
    }
done:
    if(bestR==-1) return false;
    ch->r=bestR; ch->c=bestC; ch->cand=bestMask;
    return true;
}

/* ---------- Solver helpers at file scope (no nested functions) ---------- */

// Count solutions up to 'lim' using MRV backtracking.
static int count_rec(Board* bb, Masks* mm, int lim){
    // find next cell
    bool any_empty=false;
    for(int r=0;r<N && !any_empty;r++)
        for(int c=0;c<N;c++)
            if(!bb->grid[r][c]) { any_empty=true; break; }
    if(!any_empty) return 1;

    Choice ch;
    if(!find_best_cell(bb,mm,&ch)) return 0;

    int total=0;
    unsigned cand=ch.cand;
    while(cand){
        unsigned bit=cand & -cand; cand ^= bit;
        int v=lsb_index(bit)+1;
        apply_set(bb,mm,ch.r,ch.c,v);
        total += count_rec(bb,mm,lim-total);
        apply_clear(bb,mm,ch.r,ch.c);
        if(total>=lim) return total;
    }
    return total;
}

static int count_solutions(Board* b, int limit){
    Masks m; masks_init(&m,b);
    Board tmp=*b;
    return count_rec(&tmp,&m,limit);
}

// Solve in-place; returns true if solved.
static bool solve_rec(Board* bb, Masks* mm){
    // Are we complete?
    bool any_empty=false;
    for(int r=0;r<N && !any_empty;r++)
        for(int c=0;c<N;c++)
            if(!bb->grid[r][c]) { any_empty=true; break; }
    if(!any_empty) return true;

    Choice ch;
    if(!find_best_cell(bb,mm,&ch)) return false;
    unsigned cand=ch.cand;
    while(cand){
        unsigned bit=cand & -cand; cand ^= bit;
        int v=lsb_index(bit)+1;
        apply_set(bb,mm,ch.r,ch.c,v);
        if(solve_rec(bb,mm)) return true;
        apply_clear(bb,mm,ch.r,ch.c);
    }
    return false;
}

static bool solve_board(Board* b){
    Masks m; masks_init(&m,b);
    return solve_rec(b,&m);
}

/* ---------------------- Generator utilities ---------------------- */

static void base_complete(Board* b){
    // Standard Latin base pattern: value = (r*3 + r/3 + c) % 9 + 1
    for(int r=0;r<N;r++)
        for(int c=0;c<N;c++)
            b->grid[r][c] = ( (r*3 + r/3 + c) % 9 ) + 1;
}

static void shuffle_array(int *a, int n){
    for(int i=n-1;i>0;i--){
        int j = rand()%(i+1);
        int t=a[i]; a[i]=a[j]; a[j]=t;
    }
}

static void permute_digits(Board* b){
    int map[10]; for(int i=1;i<=9;i++) map[i]=i;
    shuffle_array(&map[1],9);
    for(int r=0;r<N;r++) for(int c=0;c<N;c++){
        int v=b->grid[r][c];
        b->grid[r][c]=map[v];
    }
}

static void shuffle_rows_within_bands(Board* b){
    for(int band=0; band<3; band++){
        int rows[3]={band*3, band*3+1, band*3+2};
        shuffle_array(rows,3);
        int tmp[3][N];
        for(int i=0;i<3;i++) for(int c=0;c<N;c++) tmp[i][c]=b->grid[rows[i]][c];
        for(int i=0;i<3;i++) for(int c=0;c<N;c++) b->grid[band*3+i][c]=tmp[i][c];
    }
}

static void shuffle_cols_within_stacks(Board* b){
    for(int stack=0; stack<3; stack++){
        int cols[3]={stack*3, stack*3+1, stack*3+2};
        shuffle_array(cols,3);
        int tmp[3][N];
        for(int i=0;i<3;i++) for(int r=0;r<N;r++) tmp[i][r]=b->grid[r][cols[i]];
        for(int i=0;i<3;i++) for(int r=0;r<N;r++) b->grid[r][stack*3+i]=tmp[i][r];
    }
}

static void shuffle_bands(Board* b){
    int bands[3]={0,1,2};
    shuffle_array(bands,3);
    Board copy=*b;
    for(int i=0;i<3;i++){
        for(int r=0;r<3;r++){
            for(int c=0;c<N;c++){
                b->grid[i*3+r][c] = copy.grid[bands[i]*3+r][c];
            }
        }
    }
}

static void shuffle_stacks(Board* b){
    int stacks[3]={0,1,2};
    shuffle_array(stacks,3);
    Board copy=*b;
    for(int i=0;i<3;i++){
        for(int c=0;c<3;c++){
            for(int r=0;r<N;r++){
                b->grid[r][i*3+c] = copy.grid[r][stacks[i]*3+c];
            }
        }
    }
}

typedef enum { DIFF_EASY, DIFF_MEDIUM, DIFF_HARD } Difficulty;

static Difficulty parse_difficulty(const char* s){
    if(!s) return DIFF_MEDIUM;
    if(strncmp(s,"easy",4)==0) return DIFF_EASY;
    if(strncmp(s,"hard",4)==0) return DIFF_HARD;
    return DIFF_MEDIUM;
}

static int target_clues(Difficulty d){
    switch(d){
        case DIFF_EASY: return 45;   // easier: more givens
        case DIFF_MEDIUM: return 36;
        case DIFF_HARD: return 27;   // harder: fewer givens
        default: return 36;
    }
}

static void generate_complete(Board* sol){
    base_complete(sol);
    permute_digits(sol);
    shuffle_rows_within_bands(sol);
    shuffle_cols_within_stacks(sol);
    shuffle_bands(sol);
    shuffle_stacks(sol);
}

// Make a puzzle from a complete solution by removing symmetric pairs,
// ensuring uniqueness via solution counting (up to 2).
static void make_puzzle(const Board* solution, Board* puzzle, Difficulty d){
    copy_board(puzzle, solution);
    int target = target_clues(d);
    int clues = N*N;

    int cells[N*N];
    for(int i=0;i<N*N;i++) cells[i]=i;
    shuffle_array(cells,N*N);

    int attempts = 0;
    for(int idx=0; idx<N*N && clues>target; idx++){
        int i=cells[idx];
        int r=i/9, c=i%9;
        int sr=8-r, sc=8-c; // symmetric cell
        if(puzzle->grid[r][c]==0) continue;

        // Try removing one or the symmetric pair
        int removed=0;
        Board test; copy_board(&test,puzzle);
        test.grid[r][c]=0; removed++;
        if(!(sr==r && sc==c) && test.grid[sr][sc]!=0){ test.grid[sr][sc]=0; removed++; }

        int sols = count_solutions(&test, 2);
        if(sols==1){
            puzzle->grid[r][c]=0;
            if(!(sr==r && sc==c)) puzzle->grid[sr][sc]=0;
            clues -= removed;
        }
        attempts++;
        if(attempts>20000) break; // safety cap
    }
}

/* ------------------------- Game UI ------------------------- */

static void print_help(void){
    puts("Commands:");
    puts("  set r c v     - place value v (1..9) at row r, col c (1..9)");
    puts("  clear r c     - clear cell at (r,c)");
    puts("  hint r c      - fill the correct value for (r,c)");
    puts("  check         - verify no rule is violated");
    puts("  solve         - fill the whole solution");
    puts("  restart       - revert to the original puzzle");
    puts("  print         - show the current board");
    puts("  help          - show this help");
    puts("  quit          - exit");
}

static bool read_line(char* buf, size_t cap){
    if(!fgets(buf,(int)cap,stdin)) return false;
    size_t n=strlen(buf);
    if(n && buf[n-1]=='\n') buf[n-1]=0;
    return true;
}

static bool parse_ints(const char* s, int* a, int need){
    int count=0;
    while(*s && count<need){
        while(*s && isspace((unsigned char)*s)) s++;
        if(!*s) break;
        char* end=NULL;
        long v=strtol(s,&end,10);
        if(s==end) return false;
        a[count++]=(int)v;
        s=end;
    }
    return count==need;
}

static bool can_place(const Board* current, const Board* fixed, int r, int c, int v){
    if(fixed->grid[r][c]) return false;
    for(int i=0;i<N;i++){
        if(current->grid[r][i]==v) return false;
        if(current->grid[i][c]==v) return false;
    }
    int br=(r/3)*3, bc=(c/3)*3;
    for(int dr=0;dr<3;dr++) for(int dc=0;dc<3;dc++)
        if(current->grid[br+dr][bc+dc]==v) return false;
    return true;
}

static bool is_complete_and_correct(const Board* current){
    for(int r=0;r<N;r++) for(int c=0;c<N;c++){
        int v=current->grid[r][c];
        if(v<1 || v>9) return false;
        for(int i=0;i<N;i++){
            if(i!=c && current->grid[r][i]==v) return false;
            if(i!=r && current->grid[i][c]==v) return false;
        }
        int br=(r/3)*3, bc=(c/3)*3;
        for(int dr=0;dr<3;dr++) for(int dc=0;dc<3;dc++){
            int rr=br+dr, cc=bc+dc;
            if(rr==r && cc==c) continue;
            if(current->grid[rr][cc]==v) return false;
        }
    }
    return true;
}

static void prompt_difficulty(Difficulty* d){
    char buf[64];
    puts("Choose difficulty: easy / medium / hard [default: medium]");
    printf("> "); fflush(stdout);
    if(!read_line(buf,sizeof(buf))) { *d=DIFF_MEDIUM; return; }
    for(char* p=buf; *p; ++p) *p=(char)tolower((unsigned char)*p);
    if(buf[0]==0) { *d=DIFF_MEDIUM; return; }
    *d = parse_difficulty(buf);
}

int main(void){
    unsigned seed = (unsigned)time(NULL) ^ (unsigned)(uintptr_t)&seed;
    srand(seed);

    Difficulty diff;
    prompt_difficulty(&diff);

    Board solution, puzzle, current, fixed;

    generate_complete(&solution);
    make_puzzle(&solution, &puzzle, diff);

    copy_board(&current, &puzzle);
    copy_board(&fixed, &puzzle); // cells != 0 are fixed

    // Safety: ensure legality & (ideally) uniqueness
    if(!is_legal(&puzzle)){
        fprintf(stderr,"Internal error: generated puzzle illegal. Regenerating...\n");
        generate_complete(&solution);
        make_puzzle(&solution, &puzzle, diff);
        copy_board(&current, &puzzle);
        copy_board(&fixed, &puzzle);
    }
    Board tmp=puzzle;
    if(count_solutions(&tmp,2)!=1){
        Board s2=puzzle;
        if(solve_board(&s2)) solution=s2;
        else generate_complete(&solution);
    }

    puts("\nSudoku");
    print_board(&current);
    puts("Type 'help' for commands.");

    char line[256];
    while(1){
        printf("\n> "); fflush(stdout);
        if(!read_line(line,sizeof(line))) break;
        char cmd[32]={0};
        int i=0,j=0;
        while(line[i] && isspace((unsigned char)line[i])) i++;
        while(line[i] && !isspace((unsigned char)line[i]) && j<(int)sizeof(cmd)-1) cmd[j++]=(char)tolower((unsigned char)line[i++]);
        cmd[j]=0;
        const char* rest = line+i;

        if(strcmp(cmd,"quit")==0 || strcmp(cmd,"q")==0 || strcmp(cmd,"exit")==0){
            puts("Bye!");
            break;
        } else if(strcmp(cmd,"help")==0 || strcmp(cmd,"h")==0){
            print_help();
        } else if(strcmp(cmd,"print")==0 || strcmp(cmd,"p")==0){
            print_board(&current);
        } else if(strcmp(cmd,"restart")==0){
            copy_board(&current,&puzzle);
            puts("Restarted.");
            print_board(&current);
        } else if(strcmp(cmd,"check")==0){
            if(!is_legal(&current)) puts("There are rule violations.");
            else if(is_complete_and_correct(&current)) puts("Looks complete and correct. Nice!");
            else puts("So far so good. No violations detected.");
        } else if(strcmp(cmd,"set")==0){
            int a[3];
            if(!parse_ints(rest,a,3)){ puts("Usage: set r c v"); continue; }
            int r=a[0]-1, c=a[1]-1, v=a[2];
            if(r<0||r>=9||c<0||c>=9||v<1||v>9){ puts("r,c in 1..9 and v in 1..9"); continue; }
            if(!can_place(&current,&fixed,r,c,v)){ puts("Illegal move (conflict or fixed cell)."); continue; }
            current.grid[r][c]=v;
            print_board(&current);
            if(is_complete_and_correct(&current)) { puts("Solved! 🎉"); }
        } else if(strcmp(cmd,"clear")==0){
            int a[2];
            if(!parse_ints(rest,a,2)){ puts("Usage: clear r c"); continue; }
            int r=a[0]-1, c=a[1]-1;
            if(r<0||r>=9||c<0||c>=9){ puts("r,c in 1..9"); continue; }
            if(fixed.grid[r][c]){ puts("That cell is a given; cannot clear."); continue; }
            current.grid[r][c]=0;
            print_board(&current);
        } else if(strcmp(cmd,"hint")==0){
            int a[2];
            if(!parse_ints(rest,a,2)){ puts("Usage: hint r c"); continue; }
            int r=a[0]-1, c=a[1]-1;
            if(r<0||r>=9||c<0||c>=9){ puts("r,c in 1..9"); continue; }
            if(fixed.grid[r][c]){ puts("That cell is a given."); continue; }
            Board s=puzzle;
            if(!solve_board(&s)){ puts("No solution found (puzzle invalid)."); continue; }
            int v=s.grid[r][c];
            if(v==0){ puts("No hint available."); continue; }
            current.grid[r][c]=v;
            printf("Hint: set (%d,%d) = %d\n", r+1, c+1, v);
            print_board(&current);
        } else if(strcmp(cmd,"solve")==0){
            Board s=current;
            if(!solve_board(&s)){
                puts("No solution from current state (there may be conflicts). Try 'check'.");
            } else {
                current=s;
                puts("Solution:");
                print_board(&current);
            }
        } else if(cmd[0]==0){
            continue;
        } else {
            puts("Unknown command. Type 'help' for options.");
        }
    }

    return 0;
}
