package multiplayer.Server;

import game.Board;
import game.Marble;
import multiplayer.Parsers.RotationParsing;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * GameHandler is a class that handles a game session between 2 players. Every time a player
 * queue is over 2 players, a GameHandler object is created which hosts a board and
 * the 2 players sessions.
 *
 */
public class GameHandler {

    private final Map<ClientHandler, String> players;
    private final Board board;
    private final RotationParsing rotationParsing = new RotationParsing();
    private final Server server;
    private ClientHandler player1;
    private ClientHandler player2;


//CONSTRUCTOR

    //I did not personally feel the need of adding a list of games as
    //specified in the grading rubric, mostly because for each game,
    //one of these GameHandler objects is separately created. At the end of
    //a game, this object will be erased by the JVM garbage collection.
    public GameHandler(Map<ClientHandler, String> players, Board board, Server server) {
        this.players = players;
        this.board = board;
        this.server = server;
    }
    ///////////////////////////////////////////////////////////////////////////////////////////////

    /**
     * Sends a move to the winner player (at the end of the match).
     * @param ch receiving client
     * @param input string to be sent
     */
    protected void sendMoveToWinner(ClientHandler ch, String input) {
        ch.sendCommandToPlayer(input);
    }

    /**
     * Sends a move to both players (e.g. MOVE )
     * @param input string to be sent
     */
    protected void sendMoveToPlayers(String input) {
        for (ClientHandler ch :
                players.keySet()) {
            ch.sendCommandToPlayer(input);
        }
    }

    /**
     * Synchronizes the board of both participant players.
     * @param index field to be set
     * @param rotation rotation to be made
     * @param marble marble to be put
     */
    protected void synchronizeBoard(int index, int rotation, Marble marble) {
        board.setField(index, marble);
        rotationParsing.parseRotationFromServer(rotation, board);
    }

    /**
     * Retrieves a list of the players in this game session.
     * @return a list of players.
     */
    public List<ClientHandler> getPlayerList() {
        return new ArrayList<>(players.keySet());
    }

    /**
     * Resets the in-queue status of the players. (set to false)
     */
    protected void resetQueueStatus() {
        for (ClientHandler ch :
                players.keySet()) {
            ch.resetInQueueStatus();
        }
    }


    /**
     * Checks whether a player has won due to their opponent disconnecting.
     */
    protected void checkPlayerWinByDisconnect() {
        List<ClientHandler> playerList = getPlayerList();
        player1 = playerList.get(0);
        player2 = playerList.get(1);
        if (!server.getClientMap().containsKey(player1)) {
            sendMoveToWinner(player2, "GAMEOVER~DISCONNECT~" + player2.getClientName());
            resetQueueStatus();
        } else if (!server.getClientMap().containsKey(player2)) {
            sendMoveToWinner(player1, "GAMEOVER~DISCONNECT~" + player1.getClientName());
            resetQueueStatus();
        }
    }

    /**
     * Switches the turns between the players (so that only one of them can legally make a move).
     */
    protected void switchTurns() {
        List<ClientHandler> playerList = getPlayerList();
        player1 = playerList.get(0);
        player2 = playerList.get(1);
        if (player1.isMyTurn()) {
            player1.setMyTurn(false);
            player2.setMyTurn(true);
        } else {
            player1.setMyTurn(true);
            player2.setMyTurn(false);
        }
    }

    /**
     * Getter for the board shared in the game session.
     * @return Board
     */
    public Board getBoard() {
        return board;
    }
}

