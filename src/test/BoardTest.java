package test;


import ai.ComputerPlayer;
import ai.NaiveAI;
import game.Board;
import game.Game;
import game.Marble;
import game.Player;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test class for our board / game logic.
 */
public class BoardTest {
    private Board board;
    private Player player1;
    private Player player2;
    private static final int DIM = Board.getDIM();

    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    @Test
    public void testIndex() {
        int index = 0;
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                assertEquals(index, board.index(i, j));
                index += 1;
            }
        }
    }

    @Test
    public void testIndexOutOfBoundsException() {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                board.setField(i, Marble.WHITE);
            }
        }
        assertThrows(ArrayIndexOutOfBoundsException.class, () -> board.setField(36, Marble.WHITE));
    }

    @Test
    public void testIsFieldIndex() {
        assertThrows(ArrayIndexOutOfBoundsException.class, () -> board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(DIM * DIM - 1));
        assertThrows(ArrayIndexOutOfBoundsException.class, () -> board.isField(DIM * DIM));
    }

    @Test
    public void testIsFieldRowCol() {
        assertFalse(board.isField(-1, 0));
        assertFalse(board.isField(0, -1));
        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(2, 2));
        assertTrue(board.isField(5, 4));
        assertTrue(board.isField(4, 5));
    }

    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(0, Marble.BLACK);
        assertEquals(Marble.BLACK, board.getField(0));
        assertEquals(Marble.EMPTY, board.getField(1));
    }

    @Test
    public void testSetAndGetFieldRowAndCol() {
        board.setField(2, 3, Marble.BLACK);
        board.setField(3, 5, Marble.WHITE);
        board.setField(4, 5, Marble.EMPTY);
        System.out.println(board.toString() + "\n");
        assertThrows(ArrayIndexOutOfBoundsException.class, () ->
                board.setField(4, 6, Marble.BLACK));
        assertEquals(board.getField(2, 3), Marble.BLACK);
        assertEquals(board.getField(3, 5), Marble.WHITE);
        assertTrue(board.isEmptyField(4, 5));
    }

    @Test
    public void testBoardIsFull() {
        for (int i = 0; i < DIM * DIM; i++) {
            board.setField(i, Marble.BLACK);
        }
        System.out.println(board.toString() + "\n");
        assertTrue(board.isFull());
    }

    @Test
    public void testBoardIsNotFull() {
        for (int i = 0; i < DIM * 5; i++) {
            board.setField(i, Marble.BLACK);
        }
        System.out.println(board.toString() + "\n");
        assertFalse(board.isFull());
    }

    @Test
    public void testBoardIsEmpty() {
        for (int i = 0; i < DIM * DIM; i++) {
            board.setField(i, Marble.WHITE);
        }
        board.clearBoard();
        assertTrue(board.isEmpty());
    }

    @Test
    public void testFirstQuadrantAntiClockwiseRotation() {
        board.clearBoard();
        board.setField(0, 0, Marble.WHITE);
        board.setField(1, Marble.BLACK);
        board.setField(7, Marble.WHITE);
        board.setField(13, Marble.BLACK);

        System.out.println("Initial state \n" + board.toString() + "\n");
        board.rotateFirstQuadrantAntiClockwise();

        assertEquals(board.getField(12), Marble.WHITE);
        assertEquals(board.getField(6), Marble.BLACK);
        assertEquals(board.getField(7), Marble.WHITE);
        assertEquals(board.getField(8), Marble.BLACK);

        System.out.println("Rotated state \n" + board.toString() + "\n");
    }

    @Test
    public void testFirstQuadrantClockwiseRotation() {
        board.clearBoard();
        board.setField(0, 0, Marble.WHITE);
        board.setField(1, Marble.BLACK);
        board.setField(7, Marble.WHITE);
        board.setField(13, Marble.BLACK);

        System.out.println("Initial state \n" + board.toString() + "\n");
        board.rotateFirstQuadrantClockwise();

        assertEquals(board.getField(2), Marble.WHITE);
        assertEquals(board.getField(8), Marble.BLACK);
        assertEquals(board.getField(7), Marble.WHITE);
        assertEquals(board.getField(6), Marble.BLACK);

        System.out.println("Rotated state \n" + board.toString() + "\n");
    }

    @Test
    public void testFirstQuadrantAntiClockwise180Rotation() {
        board.clearBoard();
        board.setField(0, Marble.WHITE);
        board.setField(1, Marble.BLACK);
        board.setField(2, Marble.WHITE);
        board.setField(14, Marble.BLACK);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateFirstQuadrantAntiClockwise();
        board.rotateFirstQuadrantAntiClockwise();

        System.out.println("180 Rotated State \n" + board.toString() + "\n");
        assertEquals(board.getField(14), Marble.WHITE);
        assertEquals(board.getField(13), Marble.BLACK);
        assertEquals(board.getField(12), Marble.WHITE);
        assertEquals(board.getField(0), Marble.BLACK);
    }

    @Test
    public void testFirstQuadrantClockwise180Rotation() {
        board.clearBoard();
        board.setField(0, Marble.WHITE);
        board.setField(1, Marble.BLACK);
        board.setField(2, Marble.WHITE);
        board.setField(14, Marble.BLACK);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateFirstQuadrantClockwise();
        board.rotateFirstQuadrantClockwise();

        System.out.println("180 Rotated State \n" + board.toString() + "\n");
        assertEquals(board.getField(14), Marble.WHITE);
        assertEquals(board.getField(13), Marble.BLACK);
        assertEquals(board.getField(12), Marble.WHITE);
        assertEquals(board.getField(0), Marble.BLACK);
    }

    @Test
    public void testSecondQuadrantAntiClockwise180Rotation() {
        board.clearBoard();
        board.setField(3, Marble.WHITE);
        board.setField(4, Marble.BLACK);
        board.setField(5, Marble.WHITE);
        board.setField(10, Marble.BLACK);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateSecondQuadrantAntiClockwise();
        board.rotateSecondQuadrantAntiClockwise();

        System.out.println("180 Rotated State \n" + board.toString() + "\n");
        assertEquals(board.getField(17), Marble.WHITE);
        assertEquals(board.getField(16), Marble.BLACK);
        assertEquals(board.getField(15), Marble.WHITE);
        assertEquals(board.getField(10), Marble.BLACK);
    }

    @Test
    public void testSecondQuadrantClockwise180Rotation() {
        board.clearBoard();
        board.setField(3, Marble.WHITE);
        board.setField(4, Marble.BLACK);
        board.setField(5, Marble.WHITE);
        board.setField(10, Marble.BLACK);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateSecondQuadrantClockwise();
        board.rotateSecondQuadrantClockwise();

        System.out.println("180 Rotated State \n" + board.toString() + "\n");
        assertEquals(board.getField(17), Marble.WHITE);
        assertEquals(board.getField(16), Marble.BLACK);
        assertEquals(board.getField(15), Marble.WHITE);
        assertEquals(board.getField(10), Marble.BLACK);
    }

    @Test
    public void testThirdQuadrantAntiClockwise180Rotation() {
        board.clearBoard();
        board.setField(18, Marble.WHITE);
        board.setField(19, Marble.BLACK);
        board.setField(20, Marble.WHITE);
        board.setField(25, Marble.BLACK);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateThirdQuadrantAntiClockwise();
        board.rotateThirdQuadrantAntiClockwise();

        System.out.println("180 Rotated State \n" + board.toString() + "\n");
        assertEquals(board.getField(32), Marble.WHITE);
        assertEquals(board.getField(31), Marble.BLACK);
        assertEquals(board.getField(30), Marble.WHITE);
        assertEquals(board.getField(25), Marble.BLACK);
    }

    @Test
    public void testThirdQuadrantClockwise180Rotation() {
        board.clearBoard();
        board.setField(18, Marble.WHITE);
        board.setField(19, Marble.BLACK);
        board.setField(20, Marble.WHITE);
        board.setField(25, Marble.BLACK);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateThirdQuadrantClockwise();
        board.rotateThirdQuadrantClockwise();

        System.out.println("180 Rotated State \n" + board.toString() + "\n");
        assertEquals(board.getField(32), Marble.WHITE);
        assertEquals(board.getField(31), Marble.BLACK);
        assertEquals(board.getField(30), Marble.WHITE);
        assertEquals(board.getField(25), Marble.BLACK);
    }

    @Test
    public void testFourthQuadrantAntiClockwise180Rotation() {
        board.clearBoard();
        board.setField(21, Marble.WHITE);
        board.setField(22, Marble.BLACK);
        board.setField(23, Marble.WHITE);
        board.setField(28, Marble.BLACK);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateFourthQuadrantAntiClockwise();
        board.rotateFourthQuadrantAntiClockwise();

        System.out.println("180 Rotated State \n" + board.toString() + "\n");
        assertEquals(board.getField(35), Marble.WHITE);
        assertEquals(board.getField(34), Marble.BLACK);
        assertEquals(board.getField(33), Marble.WHITE);
        assertEquals(board.getField(28), Marble.BLACK);
    }

    @Test
    public void testFourthQuadrantClockwise180Rotation() {
        board.clearBoard();
        board.setField(21, Marble.WHITE);
        board.setField(22, Marble.BLACK);
        board.setField(23, Marble.WHITE);
        board.setField(28, Marble.BLACK);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateFourthQuadrantClockwise();
        board.rotateFourthQuadrantClockwise();

        System.out.println("180 Rotated State \n" + board.toString() + "\n");
        assertEquals(board.getField(35), Marble.WHITE);
        assertEquals(board.getField(34), Marble.BLACK);
        assertEquals(board.getField(33), Marble.WHITE);
        assertEquals(board.getField(28), Marble.BLACK);
    }

    @Test
    public void testFirstQuadrant360Rotation() {
        board.clearBoard();
        board.setField(0, Marble.BLACK);
        board.setField(2, Marble.WHITE);
        board.setField(7, Marble.BLACK);
        board.setField(14, Marble.WHITE);
        System.out.println("Initial State \n" + board.toString() + "\n");

        board.rotateFirstQuadrantClockwise();
        board.rotateFirstQuadrantClockwise();
        board.rotateFirstQuadrantClockwise();
        board.rotateFirstQuadrantClockwise();

        System.out.println("360 Clockwise Rotated State \n" + board.toString() + "\n");

        board.rotateFirstQuadrantAntiClockwise();
        board.rotateFirstQuadrantAntiClockwise();
        board.rotateFirstQuadrantAntiClockwise();
        board.rotateFirstQuadrantAntiClockwise();

        System.out.println("360 Anticlockwise Rotated State \n" + board.toString() + "\n");

        assertEquals(board.getField(0), Marble.BLACK);
        assertEquals(board.getField(2), Marble.WHITE);
        assertEquals(board.getField(7), Marble.BLACK);
        assertEquals(board.getField(14), Marble.WHITE);


    }

    @Test
    public void testHasRow() {
        board.setField(0, Marble.WHITE);
        board.setField(1, Marble.WHITE);
        board.setField(2, Marble.WHITE);
        board.setField(3, Marble.WHITE);
        board.setField(4, Marble.WHITE);
        assertTrue(board.hasRow(Marble.WHITE));
        System.out.println(board.toString() + "\n");
        board.clearBoard();

        board.setField(0, Marble.WHITE);
        board.setField(1, Marble.WHITE);
        board.setField(2, Marble.BLACK);
        board.setField(3, Marble.WHITE);
        board.setField(4, Marble.BLACK);
        assertFalse(board.hasRow(Marble.WHITE));
        System.out.println(board.toString() + "\n");


    }

    @Test
    public void testHasColumn() {
        board.setField(4, Marble.WHITE);
        board.setField(10, Marble.WHITE);
        board.setField(16, Marble.WHITE);
        board.setField(22, Marble.WHITE);
        board.setField(28, Marble.WHITE);
        assertTrue(board.hasColumn(Marble.WHITE));
        System.out.println(board.toString() + "\n");

        board.clearBoard();
        board.setField(8, Marble.WHITE);
        board.setField(14, Marble.WHITE);
        board.setField(20, Marble.WHITE);
        board.setField(26, Marble.WHITE);
        board.setField(32, Marble.WHITE);
        assertTrue(board.hasColumn(Marble.WHITE));
        System.out.println(board.toString() + "\n");

        board.clearBoard();
        board.setField(8, Marble.WHITE);
        board.setField(14, Marble.BLACK);
        board.setField(20, Marble.WHITE);
        board.setField(26, Marble.BLACK);
        board.setField(32, Marble.WHITE);
        assertFalse(board.hasColumn(Marble.WHITE));
        System.out.println(board.toString() + "\n");
    }

    @Test
    public void testHasDiagonalDown() {
        board.setField(0, Marble.WHITE);
        board.setField(7, Marble.WHITE);
        board.setField(14, Marble.WHITE);
        board.setField(21, Marble.WHITE);
        board.setField(28, Marble.WHITE);
        assertTrue(board.hasDiagonalDown(Marble.WHITE));
        System.out.println(board.toString() + "\n");

        board.clearBoard();
        board.setField(1, Marble.WHITE);
        board.setField(8, Marble.WHITE);
        board.setField(15, Marble.WHITE);
        board.setField(22, Marble.WHITE);
        board.setField(29, Marble.WHITE);
        assertTrue(board.hasDiagonalDown(Marble.WHITE));
        System.out.println(board.toString() + "\n");

        board.clearBoard();
        board.setField(0, Marble.WHITE);
        board.setField(7, Marble.BLACK);
        board.setField(14, Marble.WHITE);
        board.setField(21, Marble.BLACK);
        board.setField(28, Marble.WHITE);
        assertFalse(board.hasDiagonalDown(Marble.WHITE));
        System.out.println(board.toString() + "\n");
    }

    @Test
    public void testHasDiagonalUp() {
        board.setField(30, Marble.WHITE);
        board.setField(25, Marble.WHITE);
        board.setField(20, Marble.WHITE);
        board.setField(15, Marble.WHITE);
        board.setField(10, Marble.WHITE);
        assertTrue(board.hasDiagonalUp(Marble.WHITE));
        System.out.println(board.toString() + "\n");

        board.clearBoard();
        board.setField(24, Marble.WHITE);
        board.setField(19, Marble.WHITE);
        board.setField(14, Marble.WHITE);
        board.setField(9, Marble.WHITE);
        board.setField(4, Marble.WHITE);
        assertTrue(board.hasDiagonalUp(Marble.WHITE));
        System.out.println(board.toString() + "\n");

        board.clearBoard();
        board.setField(30, Marble.WHITE);
        board.setField(25, Marble.BLACK);
        board.setField(20, Marble.WHITE);
        board.setField(15, Marble.BLACK);
        board.setField(10, Marble.WHITE);
        assertFalse(board.hasDiagonalUp(Marble.WHITE));
        System.out.println(board.toString() + "\n");
    }

    @Test
    public void testHasWinner() {
        board.setField(0, Marble.BLACK);
        board.setField(7, Marble.BLACK);
        board.setField(14, Marble.BLACK);
        board.setField(21, Marble.BLACK);
        board.setField(28, Marble.BLACK);
        assertTrue(board.hasWinner());
    }

    @Test
    public void testIsWinner() {
        board.setField(0, Marble.BLACK);
        board.setField(7, Marble.BLACK);
        board.setField(14, Marble.BLACK);
        board.setField(21, Marble.BLACK);
        board.setField(28, Marble.BLACK);
        assertTrue(board.isWinner(Marble.BLACK));
    }

    @Test
    public void testGameOverWhenFull() {
        for (int index = 0; index < DIM * DIM; index++) {
            board.setField(index, Marble.WHITE);
        }
        assertTrue(board.isFull());
        assertTrue(board.gameOver());
    }

    @Test
    public void testGameOverWhenWinner() {
        board.setField(0, Marble.WHITE);
        board.setField(7, Marble.WHITE);
        board.setField(14, Marble.WHITE);
        board.setField(21, Marble.WHITE);
        board.setField(28, Marble.WHITE);
        assertTrue(board.isWinner(Marble.WHITE));
        assertTrue(board.gameOver());
    }

    @Test
    public void testPlacingOnSameIndex() {
        System.out.println(board.toString() + "\n");
        board.setField(0, 0, Marble.WHITE);
        board.setField(0, 5, Marble.BLACK);
        board.setField(0, 0, Marble.BLACK);
        System.out.println("Result board \n" + board.toString());
        assertEquals(Marble.WHITE, board.getField(0, 0));
    }

    @Test
    public void testFullRandomGame() {
        System.out.println("Initial state \n" + board.toString());
        player1 = new ComputerPlayer(Marble.WHITE, new NaiveAI());
        player2 = new ComputerPlayer(Marble.BLACK, new NaiveAI());
        Game game = new Game(player1, player2);
        game.start();
        assertTrue(game.getBoard().hasWinner());
    }

    //This test has also been adapted to measure the speed at which 1.000.000 games take place.
    //The hard-coded monkey style implementation of the board actually yielded 26.9 seconds, whereas
    //this 2d array implementation yielded 35.9 seconds... Shocking! :(
    //We still decided that leaving the 2d array is alright, it looks sexier.
    //Either way, the implementations can easily be switched...
    @Test
    public void test3FullRandomGames() {
        for (int i = 0; i < 3; i++) {
            //System.out.println("Initial state \n" + board.toString());
            player1 = new ComputerPlayer(Marble.WHITE, new NaiveAI());
            player2 = new ComputerPlayer(Marble.BLACK, new NaiveAI());
            Game game = new Game(player1, player2);
            game.start();
            assertTrue(game.getBoard().hasWinner() || game.getBoard().isFull());
            game.reset();
        }
    }

}
