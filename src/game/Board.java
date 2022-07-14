package game;


import java.util.ArrayList;
import java.util.HashMap;

/**
 * Board for the Pentago game.
 *
 * @author Vlad Gosa and Yolina Yordanova
 * @version v1.0
 */
public class Board {

    /*@private invariant fields.length == DIM*DIM;
      private invariant (\forall int i; i >= 0 && i < DIM;
      (\forall int j; j >= 0 && j < DIM;
       fields[i][j]==Marble.EMPTY || fields[i][j]==Marble.WHITE || fields[i][j]==Marble.BLACK));
     @*/

    //this version uses a full 6x6 board instead of 4 separate ones.
    private static final int DIM = 6;
    private static final String ANSI_RED = "\u001B[31m";
    private static final String ANSI_RESET = "\u001B[0m";
    private static final int QDIM = DIM / 2;
    private static final String DELIM = "               ";
    private static final String SPACER = "----+----+----+----+----+----";
    private static final String[] NUMBERING = {" 00 | 01 | 02 | 03 | 04 | 05 ", SPACER,
        " 06 | 07 | 08 | 09 | 10 | 11 ", SPACER, " 12 | 13 | 14 | 15 | 16 | 17 ", SPACER,
        " 18 | 19 | 20 | 21 | 22 | 23 ", SPACER, " 24 | 25 | 26 | 27 | 28 | 29 ", SPACER,
        " 30 | 31 | 32 | 33 | 34 | 35 "};
    private static final String LINE = NUMBERING[1];
    private static final String LINE_RED_PLUS = "----+----+----" + ANSI_RED +
            "+" + ANSI_RESET + "----+----+----";

    private final Marble[][] fields;
    public HashMap<Integer, Integer> winningMoves = new HashMap<>();
    //for each next possible board, remembers the move made to reach the state of that board
    public final ArrayList<Integer> moveMade = new ArrayList<>();

    /**
     * Creates an empty 6x6 board.
     */
    /*@ensures (\forall int i; i >= 0 && i < DIM; (\forall int j; j >= 0 && j < DIM;
    fields[i][j] == Marble.EMPTY || fields[i][j] == Marble.WHITE || fields[i][j] == Marble.BLACK));
    @*/
    public Board() {
        fields = new Marble[DIM][DIM];
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                fields[row][col] = Marble.EMPTY;
            }
        }
    }

    /**
     * Receives 3x3 quadrant and rotates it clockwise.
     * @param quadrant to be rotated
     * @return rotated quadrant
     */
    private static Marble[][] rotateClockwise(Marble[][] quadrant) {
        Marble[][] rotated = new Marble[QDIM][QDIM];
        for (int row = 0; row < QDIM; row++) {
            for (int col = 0; col < QDIM; col++) {
                rotated[col][2 - row] = quadrant[row][col];
            }
        }
        return rotated;
    }

    /**
     * Receives 3x3 quadrant and rotates it counterclockwise.
     * @param quadrant to be rotated
     * @return rotated quadrant
     */
    static Marble[][] rotateCounterClockwise(Marble[][] quadrant) {
        return rotateClockwise(rotateClockwise(rotateClockwise(quadrant)));
    }

    /**
     * Creates a deep copy of the board, and it's fields.
     * @return a copy of the board.
     */
    /*@ ensures \result != this;
     ensures (\forall int i; i >= 0 && i < DIM;
     (\forall int j; j >= 0 && j < DIM; \result.fields[i][j] == this.fields[i][j]));
     @*/
    private Board deepCopy() {
        Board deepCopy = new Board();
        for (int row = 0; row < DIM; row++) {
            System.arraycopy(fields[row], 0, deepCopy.fields[row], 0, DIM);
        }
        return deepCopy;
    }

    /**
     * Clears the board by declaring every field to Marble.EMPTY.
     */
    /*@ensures (\forall int i; i >= 0 && i < DIM;
    (\forall int j; j >= 0 && j < DIM; fields[i][j] == Marble.EMPTY));
    @*/
    public void clearBoard() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                fields[i][j] = Marble.EMPTY;
            }
        }
    }

    /**
     * Check whether the board is empty.
     *
     * @return true if the board is empty.
     */
    /*@ensures (\forall int i; i >= 0 && i < DIM;
    (\forall int j; j >= 0 && j < DIM; fields[i][j] == Marble.EMPTY)) ==> \result==true;
    @*/
    public boolean isEmpty() {
        boolean result = true;
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                if (!fields[i][j].equals(Marble.EMPTY)) {
                    result = false;
                    break;
                }
            }
        }
        return result;
    }

    /**
     * Calculates the index of a given row and col combination.
     *
     * @param row the row number
     * @param col the col number
     * @return index number belonging to the (row,col).
     */
    /*@requires row >= 0 && row < DIM;
      @requires col >= 0 && col < DIM;
    @*/
    public int index(int row, int col) {
        try {
            if (row >= 0 && row < DIM && col >= 0 && col < DIM) {
                return DIM * row + col;
            }
        } catch (ArrayIndexOutOfBoundsException e) {
            System.out.println("The given row,col combination is not valid");
        }
        return -1;
    }

    /**
     * Returns true if the given index is a valid index on the board.
     *
     * @param index index of the board
     * @return true if 0 (is smaller or equal to) index (is smaller than) DIM * DIM
     */
    //@ensures index >= 0 && index < DIM * DIM ==> \result == true;
    public boolean isField(int index) {
        return isField(getRow(index), getCol(index));
    }

    /**
     * Returns true if the given row,col combination is a valid index on the board.
     *
     * @param row row on the board
     * @param col col on the board
     * @return true if 0 (is smaller or equal to) row, col (is smaller than) DIM * DIM
     */
    //@ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
    //@requires row >= 0 && row < DIM;
    //@requires col >= 0 && col < DIM;
    public boolean isField(int row, int col) {
        return row >= 0 && row < DIM && col >= 0 && col < DIM;
    }

    /**
     * Returns the index of the row on the array, given the index on the board.
     *
     * @param index on the board.
     * @return the row on which the index is located.
     */
    //@requires isField(index);
    //@ensures \result > 0 && \result < DIM;
    public int getRow(int index) {
        for (int row = 0; row < DIM; row++) {
            if (index >= (DIM * row) && index <= (DIM * row) + 5) {
                return row;
            }
        }
        throw new ArrayIndexOutOfBoundsException("The index is out of bounds");
    }

    /**
     * Returns the index of the column on the array, given the index on the board.
     *
     * @param index on the array
     * @return the column
     */
    //@requires isField(index);
    //@ensures \result > 0 && \result < DIM;
    public int getCol(int index) {
        for (int col = 0; col < DIM; col++) {
            if (index >= col && index <= DIM * getRow(index) + col) {
                return col;
            }
        }
        throw new ArrayIndexOutOfBoundsException("The index is out of bounds");
    }

    /**
     * Sets the content of the given field to the marble m
     *
     * @param row given row of the field
     * @param col given column of the field
     * @param m   marble of our choice
     */
    /*@requires isField(row,col);
      @ensures getField(row,col) == m;
    @*/
    public void setField(int row, int col, Marble m) {
        if (isEmptyField(index(row, col))) {
            fields[row][col] = m;
        }
    }

    /**
     * Sets the content of the given field to the marble m
     *
     * @param i index of the field
     * @param m marble of our choice
     */
    /*@requires isField(i);
      @ensures getField(i) == m;
    @*/
    public void setField(int i, Marble m) {
        if (isEmptyField(i)) {
            fields[getRow(i)][getCol(i)] = m;
        }
    }

    /**
     * Return the content of the field with index i.
     *
     * @param i given index
     * @return the marble from field[i]
     */
    //@requires isField(i);
    //@ensures \result == Marble.BLACK || \result == Marble.WHITE || \result == Marble.EMPTY;
    public Marble getField(int i) {
        return fields[getRow(i)][getCol(i)];
    }

    /**
     * Return the content of the field with the given (row,col) combination.
     *
     * @param row given row on the board
     * @param col given col on the board
     * @return the marble from field[index(row,col)]
     */
    //@requires isField(row,col);
    //@ensures \result == Marble.BLACK || \result == Marble.WHITE || \result == Marble.EMPTY;
    public Marble getField(int row, int col) {
        return isField(row, col) ? fields[row][col] : Marble.EMPTY;
    }

    /**
     * Returns true if the field is empty
     *
     * @param i the index of the field
     * @return true if the field is empty
     */
    /*@ requires isField(i);
        ensures getField(i) == Marble.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int i) {
        return isField(i) && getField(i) == Marble.EMPTY;
    }

    /**
     * Return true if the field is empty and the parameters are valid.
     *
     * @param row given row on the board
     * @param col given col on the board
     * @return true if the field is empty
     */
    /*@ requires isField(row,col);
        ensures getField(row,col) == Marble.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int row, int col) {
        return isField(row, col) && getField(row, col) == Marble.EMPTY;
    }

    /**
     * Checks whether all the fields are non-empty.
     *
     * @return true if board is full
     */
    /*@ensures (\forall int i; i >= 0 && i < DIM;
    (\forall int j; j >= 0 && j < DIM;
    fields[i][j] == Marble.BLACK || fields[i][j] == Marble.WHITE)) ==> \result == true;
    @*/
    public boolean isFull() {
        boolean flag = false;
        for (int i = 0; i < DIM * DIM; i++) {
            if (!isEmptyField(i)) {
                flag = true;
            } else {
                flag = false;
                break;
            }
        }
        return flag;
    }

    /**
     * Checks if there are 5 marbles of the same color in a row, in a horizontal line on the board.
     *
     * @param marble for which to check sequence
     * @return true if there is a row made by the given marble
     */
    //@requires marble==Marble.BLACK || marble == Marble.WHITE;
    public boolean hasRow(Marble marble) {
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM - 4; col++) {
                if (getField(row, col).equals(marble) &&
                        getField(row, col + 1).equals(marble) &&
                        getField(row, col + 2).equals(marble) &&
                        getField(row, col + 3).equals(marble) &&
                        getField(row, col + 4).equals(marble)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Checks if there are 5 marbles of the same color in a row, in a vertical line on the board.
     *
     * @param marble for which to check sequence
     * @return true if there is a column made by the given marble
     */
    //@requires marble==Marble.BLACK || marble == Marble.WHITE;
    public boolean hasColumn(Marble marble) {
        for (int row = 0; row < DIM - 4; row++) {
            for (int col = 0; col < DIM; col++) {
                if (getField(row, col).equals(marble) &&
                        getField(row + 1, col).equals(marble) &&
                        getField(row + 2, col).equals(marble) &&
                        getField(row + 3, col).equals(marble) &&
                        getField(row + 4, col).equals(marble)) {
                    return true;
                }
            }
        }
        return false;
    }

// This is the start of the rotational methods group.

    /**
     * Check if there are 5 marbles of the same color in a row, in a downwards diagonal.
     * @param marble to check if it has a diagonal
     * @return true if there are 5 marbles of the same color in a diagonal
     */
    //@requires marble==Marble.BLACK || marble == Marble.WHITE;
    public boolean hasDiagonalDown(Marble marble) {
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                if (getField(row, col).equals(marble) &&
                        getField(row + 1, col + 1).equals(marble) &&
                        getField(row + 2, col + 2).equals(marble) &&
                        getField(row + 3, col + 3).equals(marble) &&
                        getField(row + 4, col + 4).equals(marble)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Check if there are 5 marbles of the same color in an upwards diagonal.
     * @param marble to check if it has a diagonal
     * @return true if there are 5 marbles of the same color in a diagonal
     */
    //@requires marble==Marble.BLACK || marble == Marble.WHITE;
    public boolean hasDiagonalUp(Marble marble) {
        for (int row = 4; row < DIM; row++) {
            for (int col = 0; col < DIM - 4; col++) {
                if (getField(row, col).equals(marble) &&
                        getField(row - 1, col + 1).equals(marble) &&
                        getField(row - 2, col + 2).equals(marble) &&
                        getField(row - 3, col + 3).equals(marble) &&
                        getField(row - 4, col + 4).equals(marble)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Rotates the first quadrant of the game board clockwise.
     */
    public void rotateFirstQuadrantClockwise() {
        Marble[][] quadrant = new Marble[QDIM][QDIM];
        for (int row = 0; row < QDIM; row++) {
            System.arraycopy(fields[row], 0, quadrant[row], 0, QDIM);
        }
        quadrant = rotateClockwise(quadrant);
        for (int row = 0; row < QDIM; row++) {
            System.arraycopy(quadrant[row], 0, fields[row], 0, QDIM);
        }
    }

    /**
     * Rotates the first quadrant of the game board counterclockwise.
     */
    public void rotateFirstQuadrantAntiClockwise() {
        Marble[][] quadrant = new Marble[QDIM][QDIM];
        for (int row = 0; row < QDIM; row++) {
            System.arraycopy(fields[row], 0, quadrant[row], 0, QDIM);
        }
        quadrant = rotateCounterClockwise(quadrant);
        for (int row = 0; row < QDIM; row++) {
            System.arraycopy(quadrant[row], 0, fields[row], 0, QDIM);
        }
    }

    /**
     * Rotates the second quadrant of the game board clockwise.
     */
    public void rotateSecondQuadrantClockwise() {
        Marble[][] quadrant = new Marble[QDIM][QDIM];
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                quadrant[row][col] = fields[row][col + QDIM];
            }
        }
        quadrant = rotateClockwise(quadrant);
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                fields[row][col + QDIM] = quadrant[row][col];
            }
        }
    }

    /**
     * Rotates the second quadrant of the game board counterclockwise.
     */
    public void rotateSecondQuadrantAntiClockwise() {
        Marble[][] quadrant = new Marble[QDIM][QDIM];
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                quadrant[row][col] = fields[row][col + QDIM];
            }
        }
        quadrant = rotateCounterClockwise(quadrant);
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                fields[row][col + QDIM] = quadrant[row][col];
            }
        }
    }

    /**
     * Rotates the third quadrant of the game board clockwise.
     */
    public void rotateThirdQuadrantClockwise() {
        Marble[][] quadrant = new Marble[QDIM][QDIM];
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                quadrant[row][col] = fields[row + QDIM][col];
            }
        }
        quadrant = rotateClockwise(quadrant);
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                fields[row + QDIM][col] = quadrant[row][col];
            }
        }
    }

    /**
     * Rotates the third quadrant of the game board counterclockwise.
     */
    public void rotateThirdQuadrantAntiClockwise() {
        Marble[][] quadrant = new Marble[QDIM][QDIM];
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                quadrant[row][col] = fields[row + QDIM][col];
            }
        }
        quadrant = rotateCounterClockwise(quadrant);
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                fields[row + QDIM][col] = quadrant[row][col];
            }
        }
    }

    /**
     * Rotates the fourth quadrant of the game board clockwise.
     */
    public void rotateFourthQuadrantClockwise() {
        Marble[][] quadrant = new Marble[QDIM][QDIM];
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                quadrant[row][col] = fields[row + QDIM][col + QDIM];
            }
        }
        quadrant = rotateClockwise(quadrant);
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                fields[row + QDIM][col + QDIM] = quadrant[row][col];
            }
        }
    }

    /**
     * Rotates the fourth quadrant of the game board counterclockwise.
     */
    public void rotateFourthQuadrantAntiClockwise() {
        Marble[][] quadrant = new Marble[QDIM][QDIM];
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                quadrant[row][col] = fields[row + QDIM][col + QDIM];
            }
        }
        quadrant = rotateCounterClockwise(quadrant);
        for (int col = 0; col < QDIM; col++) {
            for (int row = 0; row < QDIM; row++) {
                fields[row + QDIM][col + QDIM] = quadrant[row][col];
            }
        }
    }
    //single rotation method for every kind of rotation :
    //Rotate quadrant 1 clockwise         => rotate(1)
    //Rotate quadrant 1 counterclockwise  => rotate(2)
    //q2,c-3   ;    q2,cc-4    ;   q3,c-5  ;   q3,cc-6 ;   q4,c-7  ;   q4,cc-8
    public void rotate(int q) {
        switch (q) {
            case 1:
                rotateFirstQuadrantClockwise();
                break;
            case 2:
                rotateFirstQuadrantAntiClockwise();
                break;
            case 3:
                rotateSecondQuadrantClockwise();
                break;
            case 4:
                rotateSecondQuadrantAntiClockwise();
                break;
            case 5:
                rotateThirdQuadrantClockwise();
                break;
            case 6:
                rotateThirdQuadrantAntiClockwise();
                break;
            case 7:
                rotateFourthQuadrantClockwise();
                break;
            case 8:
                rotateFourthQuadrantAntiClockwise();
                break;
        }
    }


//This is the end of the rotational methods group.

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     * @return the game situation as String
     */
    public String toString() {
        StringBuilder s = new StringBuilder();
        for (int i = 0; i < DIM; i++) {
            StringBuilder row = new StringBuilder();
            for (int j = 0; j < DIM; j++) {
                row.append(" ").append(getField(i, j).toString().substring(0, 1).replace("E", "  ").
                                replace("B", ANSI_RED + "B " + ANSI_RESET).replace("W", "W ")).
                        append(" ");
                if (j < DIM - 1 && j != 2) {
                    row.append("|");
                }
                if (j == 2) {
                    row.append(ANSI_RED + "|" + ANSI_RESET);
                }
            }
            s.append(row).append(DELIM).append(NUMBERING[i * 2]);
            if (i < DIM - 1 && i != 2) {
                s.append("\n").append(LINE_RED_PLUS).append(DELIM).append(NUMBERING[i * 2 + 1])
                        .append("\n");
            }
            if (i == 2) {
                s.append("\n").append(ANSI_RED).append(LINE).append(ANSI_RESET).append(DELIM).
                        append(NUMBERING[i * 2 + 1]).append("\n");
            }
        }
        return s.toString();
    }

    /**
     * Returns true if the game has a winner. This is the case when one of the
     * marks controls at least one row, column or diagonal.
     * @return true if the student has a winner.
     */
    //@ ensures isWinner(Marble.BLACK) || isWinner(Marble.WHITE) ==> \result == true;
    public boolean hasWinner() {
        return isWinner(Marble.BLACK) || isWinner(Marble.WHITE);
    }

    /**
     * Checks if the mark m has won. A mark wins if it controls at
     * least one row, column or diagonal.
     * @param marble the mark of interest
     * @return true if the mark has won
     */
    /*@ requires marble == Marble.WHITE || marble == Marble.BLACK;
    ensures hasRow(marble) || hasColumn(marble) ||
     hasDiagonalDown(marble) || hasDiagonalUp(marble) ==> \result == true;
     @*/
    public boolean isWinner(Marble marble) {
        return hasColumn(marble) || hasRow(marble) ||
                hasDiagonalDown(marble) || hasDiagonalUp(marble);
    }

    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     *
     * @return true if the game is over
     */
    //@ ensures isFull() || hasWinner() ==> \result == true;
    public boolean gameOver() {
        return isFull() || hasWinner();
    }

    /**
     * Checks whether there is a move which results in an immediate win.
     * @param marble for which to check whether it has immediate winning move.
     * @return true if there is a terminal move
     */
    //@requires marble == Marble.BLACK || marble == Marble.WHITE;
    //ensures is bull
    //@ensures isWinner(marble) ==> \result == true;
    public boolean hasNextMoveWin(Marble marble) {
        Board boardCopy = deepCopy();
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                if (isEmptyField(row, col)) {
                    boardCopy.setField(row, col, marble);
                    if (boardCopy.isWinner(marble)) {
                        return true;
                    }
                    boardCopy.setField(row, col, Marble.EMPTY);
                }
            }
        }
        return false;
    }

    /**
     * Returns the number of the sub-board, given the index on the game board.
     * @param row of the field
     * @param col of the field
     * @return number of quadrant
     */
    //@requires isField(row,col);
    //@ensures \result > 1 && \result < 4;
    public int getQuadrant(int row, int col) {
        if (row >= 0 && row < QDIM && col >= 0 && col < QDIM) {
            return 1;
        }
        if (row >= 0 && row < QDIM && col >= QDIM && col < DIM) {
            return 2;
        }
        if (row >= QDIM && row < DIM && col >= 0 && col < QDIM) {
            return 3;
        }
        if (row >= QDIM && row < DIM && col >= QDIM && col < DIM) {
            return 4;
        }
        return -1;
    }

    /**
     * Returns the number of the sub-board, given the index on the game board.
     * @param i index of the field
     * @return number of quadrant
     */
    //@requires isField(i);
    //@ensures \result > 1 && \result < 4;
    public int getQuadrant(int i) {
        return getQuadrant(getRow(i), getCol(i));
    }

    /**
     * Method used by the minimax function to determine how good a given board is,
     * in terms of the given marble.
     * The more of the same marbles in a row in any sequence, the better the score.
     * @param marble in favor of which to evaluate
     * @return the score of the given board
     */
    //@requires marble == marble.WHITE && marble == marble.BLACK;
    //@ensures \result > 0 && \result < 611;
    public int evaluateScore(Marble marble) {
        int score = 0;
        int hasNeighbour = 0;
        //horizontal sequences
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                if (getField(row, col).equals(marble) && getField(row, col + 1).equals(marble)) {
                    score = score + hasNeighbour + 1;
                    hasNeighbour++;
                } else {
                    hasNeighbour = 0;
                }
            }
        }
        //vertical sequences
        for (int row = 0; row < DIM; row++) {
            for (int col = 0; col < DIM; col++) {
                if (getField(row, col).equals(marble) && getField(row + 1, col).equals(marble)) {
                    score = score + hasNeighbour + 1;
                    hasNeighbour++;
                } else {
                    hasNeighbour = 0;
                }
            }
        }
        //upwards diagonal sequences
        for (int row = 0; row < 5; row++) {
            if (getField(row, 5 - row).equals(marble)
                    && getField(row + 1, 4 - row).equals(marble)) {
                score = score + hasNeighbour + 1;
                hasNeighbour++;
            } else {
                hasNeighbour = 0;
            }
        }
        //downwards diagonal sequences
        for (int row = 0; row < DIM; row++) {
            if (getField(row, row).equals(marble) && getField(row + 1, row + 1).equals(marble)) {
                score = score + hasNeighbour + 1;
                hasNeighbour++;
            } else {
                hasNeighbour = 0;
            }
        }
        return score;
    }

    /**
     * Returns an array of all the boards containing a possible next move for the given marble.
     * @param marble for which moves to check
     * @return array containing objects of type Board
     */
    //@requires marble == marble.WHITE && marble == marble.BLACK;
    //@ensures \result.size() >= 0 && \result.size() < 289;
    public ArrayList<Board> getAllCurrentPossibleBoards(Marble marble) {
        ArrayList<Board> possibleBoards = new ArrayList<>();
        HashMap<Integer, Integer> currentWinningMoves = new HashMap<>();
        winningMoves = currentWinningMoves;
        Board boardCopy = deepCopy();
        Board resultBoard;
        //populate array with all possible moves involving a rotation move:
        // (available fields) * 8 (rotations)
        for (int row = DIM - 1; row >= 0; row--) {
            for (int col = 0; col < Board.DIM; col++) {
                if (boardCopy.isEmptyField(row, col)) {
                    for (int q = 1; q < 9; q++) {
                        boardCopy.setField(row, col, marble);
                        boardCopy.rotate(q);
                        resultBoard = boardCopy.deepCopy();
                        resultBoard.setMoveMade(index(row, col), q);
                        //sets the last made move of that specific board
                        possibleBoards.add(resultBoard);
                        if (resultBoard.isWinner(marble)) {
                            currentWinningMoves.put(resultBoard.index(row, col), q);
                        }
                        if (q % 2 == 0) {
                            boardCopy.rotate(q - 1);
                        } else {
                            boardCopy.rotate(q + 1);
                        }
                        boardCopy.setField(row, col, Marble.EMPTY);
                    }
                }
            }
        }
        return possibleBoards;
    }

    /**
     * Returns a hashmap with the chosen winning move of the AI.
     * @return the move and rotation combination
     */
    public HashMap<Integer, Integer> getWinningMoves() {
        return winningMoves;
    }
    /**
     * Remembers the last move made on each board from method getAllCurrentPossibleBoards.
     * @param rotation the given rotation.
     * @param index the given index.
     */
    //@requires isField(index) && rotation > 0 && rotation < 9;
    //@ensures moveMade.size() == 2;
    public void setMoveMade(int index, int rotation) {
        moveMade.add(index);
        moveMade.add(rotation);
    }

    //@ensures \result.size() == 2;
    public ArrayList<Integer> getMoveMade() {
        return moveMade;
    }

    /**
     * Checks whether a move is valid or not.
     * @param board the board to verify.
     * @param index the index to verify.
     * @return true if move is valid, false otherwise.
     */
    public boolean isValidMove(Board board, int index) {
        Board tempBoard = board.deepCopy();
        return tempBoard.isField(index) && tempBoard.isEmptyField(index);
    }

    /**
     * Checks whether a rotation is valid or not, according to the protocol.
     * @param index the rotation index to verify.
     * @return true if the rotation is valid, false otherwise.
     */
    public boolean isValidRotation(int index) {
        return index >= 0 && index <= 7;
    }

    public static int getDIM() {
        return DIM;
    }
}

