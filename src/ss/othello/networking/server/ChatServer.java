package ss.othello.networking.server;

/**
 * A chat server that runs in a separate thread.
 * The start method is used to start the server once and
 * the stop method is used to stop the server after it had been started.
 */
public interface ChatServer {
    /**
     * This method starts the server. It creates a new thread
     * on the Server class and starts it. It is called only
     * after the Server constructor is called.
     */
    void start();


    /**
     * Returns the port of the server. This method returns the server port number.
     *
     * @return the server port number, between 0 and 65535.
     */
    int getPort();

    /**
     * The method that stops the server. It can be called
     * only after the server has started. It closes
     * the serverSocket, so the server can not accept more
     * connections.
     */
    void stop();

}
