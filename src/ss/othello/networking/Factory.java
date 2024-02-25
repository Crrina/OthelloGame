package ss.othello.networking;

import ss.othello.networking.client.Client;
import ss.othello.networking.server.Server;

/**
 * This class models the factory which creates servers and clients.
 */
public interface Factory {


    /**
     * Makes a new server instance.
     *
     * @param port port for server to listen on
     * @return Server created
     */
    Server makeServer(int port);


    /**
     * Makes a new Client instance.
     *
     * @return Client created
     */
    Client makeClient();


}
